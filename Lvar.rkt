#lang racket/base
(require racket/contract "pkg.rkt" racket/match)
(provide install-Lvar install-Lvar_mon)

(define (install-language name contract interpreter . passes)
  (apply install name contract (cons 'interpret interpreter) passes))

;;Lvar
;;------------------------------------------------------------------------------------
;;contracts for Lvar and Lvar_mon
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
    (cond ((and (symbol? v) (hash-ref t v #f)))
          ((symbol? v) (raise (make-exn:fail:contract:variable v "not yet defined" (current-continuation-marks))))
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

  (install-language 'Lvar form? Lvar-interpret (cons 'uniquify uniquify) (cons 'remove-complex-operands remove-complex-operands)))
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

  (install-language 'Lvar_mon mon? Lvar_mon-interpret (cons 'explicate-control explicate-control)))
;;------------------------------------------------------------------------------------
