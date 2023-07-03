#lang racket/base
(require racket/contract)
(provide (contract-out #:unprotected-submodule unsafe
                       (tag? (-> any/c boolean?))
                       (installed? (-> tag? boolean?))
                       
                       (install (opt/c (->i ((name (and/c tag? (not/c installed?)))
                                             (input-contract contract?)
                                             (handler (input-contract) (-> input-contract any))
                                             (interpreter (input-contract) (-> input-contract any)))
                                            any)))
                       (get-interpreter (-> (and/c tag? installed?) any))
                       (get-handler (-> (and/c tag? installed?) any))
                       (get-contract (-> (and/c tag? installed?) any))

                       (interpret (-> (listof (and/c tag? installed?))
                                      (and/c tag? installed?)
                                      any/c
                                      any))))

(define table (make-hasheq))

(define tag? (and/c symbol? symbol-interned?))
(define (installed? name) (hash-has-key? table name))

(define (install name input-contract handler interpreter)
  (hash-set! table name (vector input-contract handler interpreter)))
(define (get-handler name)
  (vector-ref (hash-ref table name) 1))
(define (get-contract name)
  (vector-ref (hash-ref table name) 0))
(define (get-interpreter name)
  (vector-ref (hash-ref table name) 2))

(define (interpret passes intrprt form)
  ((get-interpreter intrprt) (foldl (lambda (p i) ((get-handler p) i)) form passes)))
