#lang info
(define collection "my-compiler")
(define deps '("base"))
(define build-deps '("scribble-lib" "racket-doc" "rackunit-lib" "graph"))
(define scribblings '(("scribblings/compiler.scrbl" ())))
(define pkg-desc "Description Here")
(define version "0.0")
(define pkg-authors '())
(define license '(Apache-2.0 OR MIT))
