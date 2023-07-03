#lang racket/base
(require racket/contract)
(provide (contract-out #:unprotected-submodule unsafe
                       (tag? (-> any/c boolean?))
                       (installed? (-> tag? boolean?))
                       
                       (install (opt/c (->i ((name (and/c tag? (not/c installed?)))
                                             (input-contract contract?))
                                             #:rest (rest (listof (cons/c tag? procedure?)))
                                             any)))
                       (attach (opt/c (->i ((name (and/c tag? installed?))
                                            (op (name) (and/c tag? (not/c (lambda (op) (retrieve name op)))))
                                            (proc procedure?))
                                           any)))

                       (apply-generic (opt/c (->i ((op (name) (and/c tag? (lambda (op) (retrieve name op))))
                                                   (name (and/c tag? installed?))
                                                   (obj (name) (get-contract name)))
                                                  #:rest (rest list?)
                                                  #:pre (rest name op) (procedure-arity-includes? (retrieve name op) (add1 (length rest)))
                                                  any)))))

(define table (make-hasheq))

(define tag? (and/c symbol? symbol-interned?))
(define (installed? name) (hash-has-key? table name))

(define (install name input-contract . pairs)
  (hash-set! table name (vector input-contract (make-hasheq pairs))))
(define (retrieve name op)
  (hash-ref (vector-ref (hash-ref table name) 1) op #f))
(define (get-contract name)
  (vector-ref (hash-ref table name) 0))
(define (attach name op proc)
  (hash-set! (vector-ref (hash-ref table name) 1)
             op proc))

(define (apply-generic op name obj . args)
  (apply (retrieve name op)
         obj
         args))
