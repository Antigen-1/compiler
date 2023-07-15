#lang racket/base
(require racket/contract)
(provide (contract-out #:unprotected-submodule unsafe
                       #:exists tagged
                       (tag? (-> any/c boolean?))
                       (installed? (-> tag? boolean?))

                       (tag (opt/c (->i ((name (and/c tag? installed?)) (content (name) (get-contract name))) (result tagged))))
                       (tagged-object-tag (-> tagged any))
                       (tagged-object-content (-> tagged any))
                       
                       (install (opt/c (->i ((name (and/c tag? (not/c installed?)))
                                             (input-contract contract?))
                                             #:rest (rest (listof (cons/c tag? procedure?)))
                                             any)))
                       (attach (opt/c (->i ((name (and/c tag? installed?))
                                            (op (name) (and/c tag? (not/c (lambda (op) (retrieve name op)))))
                                            (proc procedure?))
                                           any)))
                       (get-contract (-> (and/c tag? installed?) any))

                       (apply-generic (opt/c (->i ((op tag?) (obj tagged))
                                                  #:rest (rest list?)
                                                  #:pre (rest obj op)
                                                  (let ((r (retrieve (tagged-object-tag obj) op)))
                                                    (and r (procedure-arity-includes? r (add1 (length rest)))))
                                                  any)))))

(define table (make-hasheq))

(define tag? (and/c symbol? symbol-interned?))
(define (installed? name) (hash-has-key? table name))

(struct tagged-object (tag content) #:constructor-name tag)

(define (install name input-contract . pairs)
  (hash-set! table name (vector input-contract (make-hasheq pairs))))
(define (retrieve name op)
  (hash-ref (vector-ref (hash-ref table name) 1) op #f))
(define (get-contract name)
  (vector-ref (hash-ref table name) 0))
(define (attach name op proc)
  (hash-set! (vector-ref (hash-ref table name) 1)
             op proc))

(define (apply-generic op obj . args)
  (apply (retrieve (tagged-object-tag obj) op)
         (tagged-object-content obj)
         args))
