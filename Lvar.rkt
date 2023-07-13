#lang racket/base
(require racket/contract "pkg.rkt" "instruction.rkt" racket/match racket/generator racket/dict racket/list (for-syntax racket/base racket/syntax))
(provide install-Lvar install-Lvar_mon install-Cvar install-All)

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
  (install-x86-instruction)
  
  (define assign? (list/c 'define symbol? atomic?))
  (define tail? (list/c 'return atomic?))
  (define Cvar?
    (opt/c (cons/c 'program (listof (list/c symbol? (*list/c assign? tail?))))))

  (define (Cvar-interpret form)
    (define ns (make-base-namespace))
    (eval '(define-syntax-rule (return v) v) ns)
    (match form
      ((cons 'program (list-no-order (list 'start statements) _ ...))
       (eval (cons 'begin statements) ns))))

  #; (-> Cvar Cvar)
  ;; An optional optimization
  (define (partial-evaluate form)
    ;;assoc: (list/c <var> <static> <dynamic>)
    ;;<var>: symbol?
    ;;<static>: fixnum?
    ;;<dynamic>: (or/c #f (and/c (not/c fixnum?) atomic?))
    (define sequence
      (match form
        ((cons 'program (list-no-order (list 'start statements) _ ...))
         (define (reference d v) (dict-ref d v (lambda () (make-exn:fail:contract:variable v "not yet defined" (current-continuation-marks)))))
         (define (trace d s)
           (let ((v (reference d s)))
             (cond
               ((not (cadr v)) (car v))
               ((symbol? (cadr v)) (trace d (cadr v)))
               (else s))))
         (for/fold ((dict null))
                   ((st (in-list statements)))
           (define-syntax-rule (handle h p ...)
             (let-values (((num res)
                           (for/fold ((n 0) (r null))
                                     ((v (in-list (list p ...))))
                             (cond ((symbol? v)
                                    (define l (trace dict v))
                                    (if (fixnum? l)
                                        (values (h n l) r)
                                        (values (h n (car (reference dict v))) (cons l r))))
                                   (else (values (h n v) r))))))
               (list num
                     (cond ((null? res) #f)
                           ((and (null? (cdr res)) (eq? 'h '+)) (car res))
                           (else (cons 'h (reverse res)))))))
           (cons
            (cons (if (tail? st) #f (cadr st))
                  (match (if (tail? st) (cadr st) (caddr st))
                    ((list '+ p1 p2) (handle + p1 p2))
                    ((list '- p1 p2) (handle - p1 p2))
                    ((list '- p) (handle - p))
                    ((list 'read) (list 0 '(read)))
                    (p (handle + p))))
            dict)))))
    (list 'program
          (list 'start
                (apply
                 append
                 (reverse
                  (foldl
                   (lambda (st re)
                     (cons
                      (match st
                        ;;tail position
                        ((list #f n a)
                         (cond ((and (zero? n) a) (list (list 'return a)))
                               ((not a) (list (list 'return n)))
                               ((symbol? a) (list (list 'return (list '+ n a))))
                               (else (define-values (former latter)
                                       (split-at (cons (car a) (cons n (cdr a))) 3))
                                     (if (null? latter)
                                         (list (list 'return former))
                                         (let ((nv (string->symbol (symbol->string (gensym 'ret)))))
                                           (list (list 'define nv former)
                                                 (list 'return (append (list (car a) nv) latter))))))))
                        ;;assignment
                        ((list var _ expr)
                         (if (or (not expr) (symbol? expr)) null (list (list 'define var expr)))))
                      re))
                   null
                   (reverse sequence)))))))
  (define (select-instructions form)
    (define (format-instruction template . args)
      (apply apply-generic 'format-instruction 'x86-instruction-template template args))
    (define (instruction->string ins)
      (apply-generic 'instruction->string 'x86-instruction ins))
    (define gen (generator () (let loop ((i -8))
                                (yield i)
                                (loop (- i 8)))))
    (define (handle ret expr table)
      (define (reference v)
        (hash-ref table v (lambda () (raise (make-exn:fail:contract:variable v "not yet defined" (current-continuation-marks))))))

      (define (make-address l) (cons l 'rbx))
      
      (define (stash i) (format-instruction '(movq ~i %rax) i))
      (define (load l) (format-instruction '(movq ~a %rax) l))
      (define (load-and-handle h l) (format-instruction '(~c ~a %rax) h l))
      (define (handle-immediate-data h i) (format-instruction '(~c ~i %rax) h i))
      (define (unstash l) (format-instruction '(movq %rax ~a) l))

      (define il
        (match expr
          ((list op p1 p2)
           (let ((ins (if (eq? op '+) 'addq 'subq)))
             (list (if (symbol? p1) (load (reference p1)) (stash p1))
                   ((if (symbol? p2) load-and-handle handle-immediate-data)
                    ins (if (symbol? p2) (reference p2) p2)))))
          ((list '- p)
           (list
            (if (symbol? p)
                (load (reference p))
                (stash p))
            (list 'negq '%rax)))
          ((list 'read)
           (list (list 'callq 'read_int)))
          (v (if (symbol? v) (list (load (reference v))) (list (stash v))))))
      
      (if ret
          (let ((na (make-address (gen))))
            (values (hash-set table ret na) (append il (list (unstash na)))))
          (values table il)))

    (match form
      ((cons 'program (list-no-order (list 'start statements) _ ...))
       (list 'program
             (list
              'start
              (map
               instruction->string
               (apply
                append
                (reverse
                 (car
                  (foldl
                   (lambda (st ac)
                     (define-values (t l)
                       (cond ((tail? st) (handle #f (cadr st) (cdr ac)))
                             (else (handle (cadr st) (caddr st) (cdr ac)))))
                     (cons (cons l (car ac)) t))
                   (cons null (hasheq)) statements))))))))))
  
  (apply install-language 'Cvar Cvar? Cvar-interpret (pairify partial-evaluate select-instructions)))
;;------------------------------------------------------------------------------------

;;All
;;------------------------------------------------------------------------------------
(define (install-All)
  (install 'Lvar-compiler (listof (list/c (and/c tag? installed?) tag?))
           (cons 'make-Lvar-compiler
                 (lambda (l)
                   (lambda (i) (foldl (lambda (p i) (apply-generic (cadr p) (car p) i)) i l)))))
  (install-Lvar)
  (install-Lvar_mon)
  (install-Cvar)
  
  (apply-generic 'make-Lvar-compiler 'Lvar-compiler
                 (list (list 'Lvar 'uniquify)
                       (list 'Lvar 'remove-complex-operands)
                       (list 'Lvar_mon 'explicate-control)
                       (list 'Cvar 'partial-evaluate)
                       (list 'Cvar 'select-instructions))))
;;------------------------------------------------------------------------------------
