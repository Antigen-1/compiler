#lang racket/base
(require racket/contract "pkg.rkt" racket/match)

(define (install-language name contract interpreter . passes)
  (apply install name contract (cons 'interpret interpreter) passes))

;;Lvar
;;------------------------------------------------------------------------------------
(define (install-Lvar)
  (define form/c
    (opt/c
     (recursive-contract
      (or/c fixnum? (list/c 'read) (list/c '- form/c) (list/c '- form/c form/c) (list/c '+ form/c form/c) symbol?
            (list/c 'let (list/c (list/c symbol? form/c)) form/c)))))
  
  (define (Lvar-interpret form)
    (eval form (make-base-namespace)))

  (define (reference v t)
    (cond ((and (symbol? v) (hash-has-key? t v))
                (hash-ref t v))
               ((symbol? v) (raise (make-exn:fail:contract:variable v "not yet defined" (current-continuation-marks))))
               (else v)))
  (define (n:gensym s)
    (string->symbol (symbol->string (gensym s))))
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
      ('(read) '(read))
      (v (reference v table))))

  (install-language 'Lvar form/c Lvar-interpret (cons 'uniquify uniquify)))
;;------------------------------------------------------------------------------------
