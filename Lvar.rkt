#lang racket/base
(require racket/contract "pkg.rkt" racket/match racket/list)
(provide install-Lvar install-Lvar_mon)

(define (install-language name contract interpreter . passes)
  (apply install name contract (cons 'interpret interpreter) passes))

;;Lvar
;;------------------------------------------------------------------------------------
(define (install-Lvar)
  (define form?
    (opt/c
     (recursive-contract
      (or/c fixnum? (list/c 'read) symbol?
            (list/c '- form?) (list/c '- form? form?) (list/c '+ form? form?)
            (list/c 'let (list/c (list/c symbol? form?)) form?)))))
  
  (define (Lvar-interpret form)
    (eval form (make-base-namespace)))

  (define (reference v t)
    (cond ((and (symbol? v) (hash-has-key? t v))
           (hash-ref t v))
          ((symbol? v) (raise (make-exn:fail:contract:variable v "not yet defined" (current-continuation-marks))))
          (else v)))
  (define (n:gensym s)
    (string->symbol (symbol->string (gensym s))))
  (define (primitive? v) (or (symbol? v) (fixnum? v) (equal? v '(read))))
  
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
    (match form
      ((list 'let (list (list v e)) f)
       (list 'let (list (list v (if (primitive? e) e (remove-complex-operands e))))
             (if (primitive? f) f (remove-complex-operands f))))
      ((list '- form)
       (if (primitive? form)
           (list '- form)
           (let ((nv (n:gensym 'tmp)))
             (list 'let (list (list nv (remove-complex-operands form)))
                   (list '- nv)))))
      ((list op form1 form2)
       (cond ((and (primitive? form1) (primitive? form2))
              (list op form1 form2))
             ((primitive? form1)
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
                                 (list op nv1 nv2)))))))
      (v v)))

  (install-language 'Lvar form? Lvar-interpret (cons 'uniquify uniquify) (cons 'remove-complex-operands remove-complex-operands)))
;;------------------------------------------------------------------------------------

;;Lvar_mon
;;------------------------------------------------------------------------------------
(define (install-Lvar_mon)
  (define primitive? (or/c symbol? fixnum?))
  (define atomic? (or/c primitive? (list/c '- primitive?) (list/c '- primitive? primitive?) (list/c '+ primitive? primitive?) (list/c 'read)))
  (define form? (opt/c (recursive-contract (or/c atomic? (list/c 'let (list/c (list/c symbol? form?)) form?)))))

  (define (Lvar_mon-interpret form)
    (eval form (make-base-namespace)))
  
  #; (-> Lvar_mon Cvar)
  (define (explicate-control form)
    (let-values (((former latter)
                  (split-at-right
                   (let loop ((form form))
                     (match form
                       ((list 'let (list (list v e)) f)
                        (if (atomic? e)
                            (cons (list 'define v e) (loop f))
                            (let-values (((former latter) (split-at-right (loop e) 1)))
                              (append former (cons (list 'define v (car latter)) (loop f))))))
                       (v (list v))))
                   1)))
      (list 'program (list 'start (append former (list (cons 'return latter)))))))

  (install-language 'Lvar_mon form? Lvar_mon-interpret (cons 'explicate-control explicate-control)))
;;------------------------------------------------------------------------------------
