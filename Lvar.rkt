#lang racket/base
(require racket/contract "pkg.rkt" racket/match (for-syntax racket/base racket/syntax))
(provide install-Lvar install-Lvar_mon install-Cvar)

(define (install-language name contract interpreter . passes)
  (apply install name contract (cons 'interpret interpreter) passes))

(define-syntax-rule (pairify id ...) (list (cons 'id id) ...))

;;Lvar
;;------------------------------------------------------------------------------------
;;common contracts
(define primitive? (or/c symbol? fixnum?))
(define atomic?
  (or/c primitive?
        (list/c 'read) (list/c '- primitive?) (list/c '- primitive? primitive?) (list/c '+ primitive? primitive?)))
(define mon? (opt/c (recursive-contract (or/c atomic? (list/c 'let (list/c (list/c symbol? mon?)) mon?)) #:flat)))

(define (install-Lvar)
  (define form?
    (opt/c
     (recursive-contract
      (or/c primitive?
            (list/c '- form?) (list/c '- form? form?) (list/c '+ form? form?) (list/c 'read)
            (list/c 'let (list/c (list/c symbol? form?)) form?)))))
  
  (define (Lvar-interpret form)
    (eval form (make-base-namespace)))

  (define (reference v t)
    (cond ((symbol? v) (hash-ref t v (lambda () (raise (make-exn:fail:contract:variable v "not yet defined" (current-continuation-marks))))))
          (else v)))
  (define (n:gensym s)
    (string->symbol (symbol->string (gensym s))))
  
  #; (-> Lvar |restricted Lvar|)
  (define (uniquify form (table (hasheq)))
    (match form
      ((list 'let (list (list v e)) f)
       (define-values (nv nt)
         (let ((new-v (n:gensym v)))
           (values new-v (hash-set table v new-v))))
       (list 'let (list (list nv (uniquify e table))) (uniquify f nt)))
      ((list '- form) (list '- (uniquify form table)))
      ((list '- form1 form2) (list '- (uniquify form1 table) (uniquify form2 table)))
      ((list '+ form1 form2) (list '+ (uniquify form1 table) (uniquify form2 table)))
      (v (reference v table))))
  #; (-> Lvar Lvar_mon)
  (define (remove-complex-operands form)
    (if (mon? form)
        form
        (match form
          ((list 'let (list (list v e)) f)
           (list 'let (list (list v (remove-complex-operands e)))
                 (remove-complex-operands f)))
          ((list '- form)
           (let ((nv (n:gensym 'tmp)))
             (list 'let (list (list nv (remove-complex-operands form)))
                   (list '- nv))))
          ((list op form1 form2)
           (cond ((primitive? form1)
                  (let ((nv (n:gensym 'tmp)))
                    (list 'let (list (list nv (remove-complex-operands form2)))
                          (list op form1 nv))))
                 ((primitive? form2)
                  (let ((nv (n:gensym 'tmp)))
                    (list 'let (list (list nv (remove-complex-operands form1)))
                          (list op nv form2))))
                 (else (let ((nv1 (n:gensym 'tmp))
                             (nv2 (n:gensym 'tmp)))
                         (list 'let (list (list nv1 (remove-complex-operands form1)))
                               (list 'let (list (list nv2 (remove-complex-operands form2)))
                                     (list op nv1 nv2))))))))))

  (apply install-language 'Lvar form? Lvar-interpret (pairify uniquify remove-complex-operands)))
;;------------------------------------------------------------------------------------

;;Lvar_mon
;;------------------------------------------------------------------------------------
(define (install-Lvar_mon)

  (define (Lvar_mon-interpret form)
    (eval form (make-base-namespace)))
  
  #; (-> Lvar_mon Cvar)
  (define (explicate-control form)
    (define (make-continuation ret expr)
      (if ret (list 'define ret expr) (list 'return expr)))
    
    (let ((seq
           (let loop ((ret #f) (form form))
             (if (atomic? form)
                 (list (make-continuation ret form))
                 (match form
                   ((list 'let (list (list v e)) f)
                    (append (loop v e) (loop ret f))))))))
      (list 'program (list 'start seq))))

  (apply install-language 'Lvar_mon mon? Lvar_mon-interpret (pairify explicate-control)))
;;------------------------------------------------------------------------------------

;;Cvar
;;------------------------------------------------------------------------------------
(define (install-Cvar)
  (define assign? (list/c 'define symbol? atomic?))
  (define tail? (list/c 'return atomic?))
  (define Cvar?
    (opt/c (cons/c 'program (listof (list/c symbol? (*list/c assign? tail?))))))

  (define (Cvar-interpret form)
    (define ns (make-base-namespace))
    (eval '(define-syntax-rule (return v) v) ns)
    (match form
      ((cons 'program (list-no-order (list 'start (list statement ...)) _ ...))
       (eval (cons 'begin statement) ns))))

  #; (-> Cvar Cvar)
  (define (partial-evaluate form)
    (define (simplify expr table)
      (define (reference p)
        (cond ((symbol? p) (hash-ref table p #f)) (else p)))
      (define-syntax (handle stx)
        (syntax-case stx ()
          ((_ h p ...)
           (with-syntax (((np ...) (map generate-temporary (syntax->datum #'(p ...)))))
             #'(let ((np (reference p)) ...)
                 (if (and np ...)
                     (h np ...)
                     (cons 'h
                           (map
                            (lambda (r o) (or r o))
                            (list np ...) (list p ...)))))))))
      (match expr
        ((list '+ p1 p2)
         (handle + p1 p2))
        ((list '- p)
         (handle - p))
        ((list '- p1 p2)
         (handle - p1 p2))
        ((list 'read)
         (list 'read))
        (p (cond ((reference p)) (else p)))))
    (define (optimize statement table)
      (cond ((tail? statement)
             (list 'return (simplify (cadr statement) table)))
            (else
             (define r (simplify (caddr statement) table))
             ;;`(define <var> <var>)` forms are also removed from the sequence
             ;;so that I don't need a `patch_instructions` pass.
             ;;Of course, it is not necessary for typical partial evaluators to implement this feature
             (if (primitive? r)
                 (hash-set table (cadr statement) r)
                 (list 'define (cadr statement) r)))))
    (cons 'program
          (map
           (lambda (block)
             (list (car block)
                   (let-values (((t r)
                                 (for/fold ((table (hasheq)) (result null))
                                           ((statement (in-list (cadr block))))
                                   (define r (optimize statement table))
                                   (cond ((hash? r) (values r result))
                                         (else (values table (cons r result)))))))
                     (reverse r))))
           (cdr form))))
  
  (apply install-language 'Cvar Cvar? Cvar-interpret (pairify partial-evaluate)))
;;------------------------------------------------------------------------------------
