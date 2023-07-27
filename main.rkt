#lang racket/base

(module+ test
  (require rackunit))

;; Notice
;; To install (from within the package directory):
;;   $ raco pkg install
;; To install (once uploaded to pkgs.racket-lang.org):
;;   $ raco pkg install <<name>>
;; To uninstall:
;;   $ raco pkg remove <<name>>
;; To view documentation:
;;   $ raco docs <<name>>
;;
;; For your convenience, we have included LICENSE-MIT and LICENSE-APACHE files.
;; If you would prefer to use a different license, replace those files with the
;; desired license.
;;
;; Some users like to add a `private/` directory, place auxiliary files there,
;; and require them in `main.rkt`.
;;
;; See the current version of the racket style guide here:
;; http://docs.racket-lang.org/style/index.html

;; Code here



(module+ test
  ;; Any code in this `test` submodule runs when this file is run using DrRacket
  ;; or with `raco test`. The code here does not run when this file is
  ;; required by another module.

  (check-equal? (+ 2 2) 4))

(require "pkg.rkt" "Lvar.rkt" racket/contract racket/set)

;;All
;;------------------------------------------------------------------------------------
(define (install-All name)
  (install 'compiler (listof (cons/c (and/c tag? installed?) (cons/c tag? (cons/c boolean? list?))))
           (cons 'make-compiler
                 (lambda (l)
                   (lambda (i (f #t))
                     (foldl
                      (lambda (p i) (if (or f (caddr p)) (apply apply-generic (cadr p) (tag (car p) i) (cdddr p)) i))
                      i l)))))
  (define table
    (hasheq 'Lvar1
            (lambda ()
              (install-Lvar)
              (install-Lvar_mon)
              (install-Cvar)
              (install-X86int)
              (install-X86raw)
              
              (apply-generic 'make-compiler
                             (tag
                              'compiler
                              (list (list 'Lvar 'uniquify #t)
                                    (list 'Lvar 'remove-complex-operands #t)
                                    (list 'Lvar_mon 'explicate-control #t)
                                    (list 'Cvar 'partial-evaluate #f)
                                    (list 'Cvar 'select-instructions #t)
                                    (list 'X86int 'patch-instructions #t)
                                    (list 'X86int 'assign-home #t)
                                    (list 'X86raw 'make-text #t)))))
            'Lvar2
            (lambda ()
              (install-Lvar)
              (install-Lvar_mon)
              (install-Cvar)
              (install-Cvar_conflicts)
              (install-X86int)
              (install-X86raw)

              (apply-generic 'make-compiler
                             (tag
                              'compiler
                              (list (list 'Lvar 'uniquify #t)
                                    (list 'Lvar 'remove-complex-operands #t)
                                    (list 'Lvar_mon 'explicate-control #t)
                                    (list 'Cvar 'partial-evaluate #f)
                                    (list 'Cvar 'find-conflicts #t (seteq -2 -1))
                                    (list 'Cvar_conflicts 'allocate-registers #t)
                                    (list 'X86int 'patch-instructions #t)
                                    (list 'X86int 'assign-home #t)
                                    (list 'X86raw 'make-text #t)))))))
  
  ((hash-ref table name)))
;;------------------------------------------------------------------------------------

