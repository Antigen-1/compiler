#lang racket/base
(require "pkg.rkt" "instruction.rkt" racket/match racket/contract)

(define (make-instruction-selector number->location variable->number)
  (define (move s d) (list 'movq s d))
  (define (compute h . a) (cons h a))
  (define (make-token p)
    (if (symbol? p) (number->location (variable->number p)) p))

  (define primitive? (or/c symbol? fixnum?))
  
  (define/contract (handle ret expr)
    (-> (or/c symbol? exact-integer?) (or/c primitive?
                                            (list/c '+ primitive? primitive?)
                                            (list/c '- primitive?)
                                            (list/c '- primitive? primitive?)
                                            (list/c 'read))
        any)
    (define num (if (exact-integer? ret) ret (variable->number ret)))
    (define return-location (number->location num))
    (match expr
      ((list '+ arg1 arg2)
       #:when (and (symbol? arg2) (= (variable->number arg2) num))
       (list (compute 'addq (make-token arg1) return-location)))
      ((list '- arg1 arg2)
       #:when (and (symbol? arg2) (= (variable->number arg2) num))
       (list
        (move (make-token arg2) "rax")
        (move (make-token arg1) return-location)
        (compute 'subq "rax" return-location)))
      ((list op arg1 arg2)
       (let ((ins (if (eq? op '+) 'addq 'subq)))
         (append
          (if (and (symbol? arg1) (= (variable->number arg1) num)) null (list (move (make-token arg1) return-location)))
          (list (compute ins (make-token arg2) return-location)))))
      ((list '- arg)
       (append
        (if (and (symbol? arg) (= (variable->number arg) num)) null (list (move (make-token arg) return-location)))
        (list (compute 'negq return-location))))
      ((list 'read)
       (list (compute 'callq 'read_int)
             (move "rax" return-location)))
      (v (if (and (symbol? v) (= (variable->number v) num))
             null
             (list (move (make-token v) return-location))))))

  handle)

;;This package is installed when the module is instantiated.
(install 'selector (list/c (-> any/c argument?) (-> any/c exact-integer?))
         (cons 'make-instruction-selector (lambda (ls) (apply make-instruction-selector ls))))
