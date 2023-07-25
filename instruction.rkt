#lang racket/base
(require racket/contract racket/match racket/string "pkg.rkt")
(provide resolve-label
         register? address? immediate? label? command? argument?)

(define register? (or/c string? (list/c '~r string?)))
(define address? (or/c (cons/c fixnum? string?) (list/c '~a (cons/c fixnum? string?))))
(define immediate? (or/c fixnum? (list/c '~i fixnum?)))
(define label? (or/c symbol? (list/c '~l symbol?)))
(define command? (or/c symbol? (list/c '~c symbol?)))
(define argument? (or/c register? address? immediate? label?))
(define instruction? (cons/c command? (listof argument?)))
(define block? (list/c symbol? (listof instruction?)))
(define template? (cons/c (or/c '~c symbol?) (listof (or/c '~l '~r '~a '~i (cons/c fixnum? string?) string? symbol? fixnum?))))

(define (resolve-label s) (if (eq? (system-type 'os) 'macosx) (string-append "_" (symbol->string s)) (symbol->string s)))

(define (format-instruction template . args)
  (reverse
   (car
    (foldl
     (lambda (p a)
       (case p
         ((~c ~r ~a ~i ~l) (cons (cons (list p (cadr a)) (car a)) (cddr a)))
         (else (cons (cons p (car a)) (cdr a)))))
     (cons null args) template))))
(define (instruction->string ins)
  (define (string-list-join sl)
    (string-append (car sl) (string-join (cdr sl) "," #:before-first " ") "\n"))
  (string-list-join
   (cons
    (match (car ins)
      ((list '~c s) (symbol->string s))
      (s (symbol->string s)))
    (map
     (lambda (i)
       (match i
         ((list '~r s) (format "%~a" s))
         ((list '~a (cons f r)) (format "~a(%~a)" f r))
         ((list '~i f) (format "$~a" f))
         ((list '~l s) (resolve-label s))
         ((cons f r) (format "~a(%~a)" f r))
         (v (cond ((symbol? v) (resolve-label v))
                  ((fixnum? v) (format "$~a" v))
                  (else (format "%~a" v))))))
     (cdr ins)))))
(define (block->string block)
  (string-append (resolve-label (car block)) ":\n"
                 (string-join (map instruction->string (cadr block)) #:before-first " ")))

;; These packages are installed when this module is instantiated.
(install 'x86-instruction-template template? (cons 'format-instruction format-instruction))
(install 'x86-instruction instruction? (cons 'instruction->string instruction->string))
(install 'x86-instruction-block block? (cons 'block->string block->string))
