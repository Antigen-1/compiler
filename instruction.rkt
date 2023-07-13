#lang racket/base
(require racket/contract racket/match racket/string racket/format "pkg.rkt")
(provide install-x86-instruction-template install-x86-instruction install-x86-instruction-block)

(define register? (list/c '~r symbol?))
(define address? (list/c '~a (cons/c fixnum? symbol?)))
(define integer? (list/c '~i fixnum?))
(define label? (list/c '~l symbol?))
(define command? (list/c '~c symbol?))
(define argument? (or/c register? address? integer? label?))
(define instruction? (cons/c (or/c command? symbol?) (listof (or/c argument? (cons/c fixnum? symbol?) symbol? fixnum?))))
(define block? (list/c symbol? (listof instruction?)))
(define template? (cons/c (or/c '~c symbol?) (listof (or/c '~l '~r '~a '~i (cons/c fixnum? symbol?) symbol? fixnum?))))

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
   (map
    (lambda (i)
      (match i
        ((list '~r s) (format "%~a" s))
        ((list '~a (cons f r)) (format "~a(%~a)" f r))
        ((list '~i f) (format "$~a" f))
        ((list '~l s) (resolve-label s))
        ((list '~c s) (~a s))
        ((cons f r) (format "~a(%~a)" f r))
        (v (if (symbol? v) (~a v) (format "$~a" v)))))
    ins)))
(define (block->string block)
  (string-append (resolve-label (car block)) ":\n"
                 (string-join (map instruction->string (cadr block)) #:before-first " ")))

(define (install-x86-instruction-template)
  (install 'x86-instruction-template template? (cons 'format-instruction format-instruction)))
(define (install-x86-instruction)
  (install 'x86-instruction instruction? (cons 'instruction->string instruction->string)))
(define (install-x86-instruction-block)
  (install 'x86-instruction-block block? (cons 'block->string block->string)))
