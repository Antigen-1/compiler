#lang racket/base
(require racket/contract "pkg.rkt" "instruction.rkt" racket/match racket/generator racket/dict racket/list racket/string (for-syntax racket/base))
(provide install-Lvar install-Lvar_mon install-Cvar install-X86raw install-All)

(define (install-language name contract interpreter . passes)
  (apply install name contract (cons 'interpret interpreter) passes))

(define-syntax-rule (pairify id ...) (list (cons 'id id) ...))

;;Lvar
;;------------------------------------------------------------------------------------
;;common contracts
(define primitive? (or/c symbol? fixnum?))
(define atomic?
  (or/c primitive?
        (list/c 'read) (list/c '- primitive?) (list/c '- primitive? primitive?) (list/c '+ primitive? primitive?)))
(define mon? (opt/c (recursive-contract (or/c atomic? (list/c 'let (list/c (list/c symbol? mon?)) mon?)) #:flat)))

(define (install-Lvar)
  (define form?
    (opt/c
     (recursive-contract
      (or/c primitive?
            (list/c '- form?) (list/c '- form? form?) (list/c '+ form? form?) (list/c 'read)
            (list/c 'let (list/c (list/c symbol? form?)) form?)))))
  
  (define (Lvar-interpret form)
    (eval form (make-base-namespace)))

  (define (reference v t)
    (cond ((symbol? v) (hash-ref t v (lambda () (raise (make-exn:fail:contract:variable v "not yet defined" (current-continuation-marks))))))
          (else v)))
  (define (n:gensym s)
    (string->symbol (symbol->string (gensym s))))
  
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
    (if (mon? form)
        form
        (match form
          ((list 'let (list (list v e)) f)
           (list 'let (list (list v (remove-complex-operands e)))
                 (remove-complex-operands f)))
          ((list '- form)
           (let ((nv (n:gensym 'tmp)))
             (list 'let (list (list nv (remove-complex-operands form)))
                   (list '- nv))))
          ((list op form1 form2)
           (cond ((primitive? form1)
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
                                     (list op nv1 nv2))))))))))

  (apply install-language 'Lvar form? Lvar-interpret (pairify uniquify remove-complex-operands)))
;;------------------------------------------------------------------------------------

;;Lvar_mon
;;------------------------------------------------------------------------------------
(define (install-Lvar_mon)

  (define (Lvar_mon-interpret form)
    (eval form (make-base-namespace)))
  
  #; (-> Lvar_mon Cvar)
  (define (explicate-control form)
    (define (make-continuation ret expr)
      (if ret (list 'define ret expr) (list 'return expr)))
    
    (let ((seq
           (let loop ((ret #f) (form form))
             (if (atomic? form)
                 (list (make-continuation ret form))
                 (match form
                   ((list 'let (list (list v e)) f)
                    (append (loop v e) (loop ret f))))))))
      (list 'program (list 'start seq))))

  (apply install-language 'Lvar_mon mon? Lvar_mon-interpret (pairify explicate-control)))
;;------------------------------------------------------------------------------------

;;Cvar
;;------------------------------------------------------------------------------------
(define (install-Cvar)
  (install-x86-instruction-template)
  
  (define assign? (list/c 'define symbol? atomic?))
  (define tail? (list/c 'return atomic?))
  (define Cvar?
    (opt/c (list/c 'program (list/c 'start (*list/c assign? tail?)))))

  (define (Cvar-interpret form)
    (define ns (make-base-namespace))
    (eval '(define-syntax-rule (return v) v) ns)
    (match form
      ((list 'program (list 'start statements))
       (eval (cons 'begin statements) ns))))

  #; (-> Cvar Cvar)
  ;; An optional optimization
  (define (partial-evaluate form)
    ;;assoc: (list/c <var> <static> <dynamic>)
    ;;<var>: symbol?
    ;;<static>: fixnum?
    ;;<dynamic>: (or/c #f <var> (list/c '+ <var> <var>) (list/c '- <var> <var>) (list/c '- <var>) (list/c 'read))
    (define sequence
      (match form
        ((list 'program (list 'start statements))
         (define (reference d v) (dict-ref d v (lambda () (make-exn:fail:contract:variable v "not yet defined" (current-continuation-marks)))))
         (define (trace d s)
           (let ((v (reference d s)))
             (cond
               ((not (cadr v)) (car v))
               ((symbol? (cadr v)) (trace d (cadr v)))
               (else s))))
         (for/fold ((dict null))
                   ((st (in-list statements)))
           (define-syntax-rule (handle h p ...)
             (let-values (((st dy)
                           (for/fold ((n null) (r null))
                                     ((v (in-list (list p ...))))
                             (cond ((symbol? v)
                                    (define l (trace dict v))
                                    (if (fixnum? l)
                                        (values (cons l n) r)
                                        (values (cons (car (reference dict v)) n) (cons l r))))
                                   (else (values (cons v n) r))))))
               (list (apply h (reverse st))
                     (match* (dy 'h (list p ...))
                       (((list) _ _) #f)
                       (((list a) '+ _) a)
                       (((list a) '- (cons a0 (cons a1 _))) #:when (eq? a a0) a)
                       ((l q _) (cons q (reverse l)))))))
           (cons
            (cons (if (tail? st) #f (cadr st))
                  (match (if (tail? st) (cadr st) (caddr st))
                    ((list '+ p1 p2) (handle + p1 p2))
                    ((list '- p1 p2) (handle - p1 p2))
                    ((list '- p) (handle - p))
                    ((list 'read) (list 0 '(read)))
                    (p (handle + p))))
            dict)))))
    (list 'program
          (list 'start
                (apply
                 append
                 (reverse
                  (foldl
                   (lambda (st re)
                     (cons
                      (match st
                        ;;tail position
                        ((list #f n a)
                         (cond ((and (zero? n) a) (list (list 'return a)))
                               ((not a) (list (list 'return n)))
                               ((symbol? a) (list (list 'return (list '+ n a))))
                               (else (define-values (former latter)
                                       (split-at (cons (car a) (cons n (cdr a))) 3))
                                     ;;n '(- a) => '(- n a)
                                     ;;n '(- a1 a2) => '(+ n a1) '(a2)
                                     ;;n '(+ a1 a2) => '(+ n a1) '(a2)
                                     (if (null? latter)
                                         (list (list 'return former))
                                         (let ((nv (string->symbol (symbol->string (gensym 'ret)))))
                                           (list (list 'define nv (cons '+ (cdr former)))
                                                 (list 'return (append (list (car a) nv) latter))))))))
                        ;;assignment
                        ((list var _ expr)
                         (if (or (not expr) (symbol? expr)) null (list (list 'define var expr)))))
                      re))
                   null
                   (reverse sequence)))))))
  (define (select-instructions form)
    (define (format-instruction template . args)
      (apply apply-generic 'format-instruction 'x86-instruction-template template args))
    (define gen (generator () (let loop ((i -8))
                                (yield i)
                                (loop (- i 8)))))
    (define (handle ret expr table)
      (define (reference v)
        (hash-ref table v (lambda () (raise (make-exn:fail:contract:variable v "not yet defined" (current-continuation-marks))))))

      (define (make-address l) (cons l 'rbp))
      
      (define (stash i) (format-instruction '(movq ~i %rax) i))
      (define (load l) (format-instruction '(movq ~a %rax) l))
      (define (load-and-handle h l) (format-instruction '(~c ~a %rax) h l))
      (define (handle-immediate-data h i) (format-instruction '(~c ~i %rax) h i))
      (define (unstash l) (format-instruction '(movq %rax ~a) l))

      (define il
        (match expr
          ((list op p1 p2)
           (let ((ins (if (eq? op '+) 'addq 'subq)))
             (list (if (symbol? p1) (load (reference p1)) (stash p1))
                   ((if (symbol? p2) load-and-handle handle-immediate-data)
                    ins (if (symbol? p2) (reference p2) p2)))))
          ((list '- p)
           (list
            (if (symbol? p)
                (load (reference p))
                (stash p))
            (list 'negq '%rax)))
          ((list 'read)
           (list (list 'callq 'read_int)))
          (v (if (symbol? v) (list (load (reference v))) (list (stash v))))))
      
      (if ret
          (let ((na (make-address (gen))))
            (values (hash-set table ret na) (append il (list (unstash na)))))
          (values table il)))
    
    (match form
      ((list 'program (list 'start statements))
       (define block
         (list
          'start
          (apply
           append
           (reverse
            (cons
             (list '(jmp (~l conclusion)))
             (car
              (foldl
               (lambda (st ac)
                 (define-values (t l)
                   (cond ((tail? st) (handle #f (cadr st) (cdr ac)))
                         (else (handle (cadr st) (caddr st) (cdr ac)))))
                 (cons (cons l (car ac)) t))
               (cons null (hasheq)) statements)))))))
       (define stack-size
         (let ((c (gen)))
           (let-values (((q r) (quotient/remainder (abs (+ c 8)) 16)))
             (if (zero? r) (* 16 q) (* 16 (add1 q))))))
       (list 'program (pairify stack-size) block))))
  
  (apply install-language 'Cvar Cvar? Cvar-interpret (pairify partial-evaluate select-instructions)))
;;------------------------------------------------------------------------------------

;;X86int
;;------------------------------------------------------------------------------------
(define (install-X86int)
  (install-x86-instruction)

  (define form? (opt/c (list/c 'program (list/c (cons/c 'stack-size fixnum?)) (list/c 'start (listof (get-contract 'x86-instruction))))))
  
  (define (assign-home form)
    (match form
      ((list 'program (list (cons 'stack-size stack-size)) block)
       (list
        'program
        block
        (list
         'main
         (if (zero? stack-size)
             (list '(jmp (~l start)))
             (list '(pushq %rbp)
                   '(movq %rsp %rbp)
                   (list 'subq stack-size '%rsp)
                   '(jmp (~l start)))))
        (list
         'conclusion
         (if (zero? stack-size)
             (list '(retq))
             (list (list 'addq stack-size '%rsp)
                   '(popq %rbp)
                   '(retq))))))))

  (apply install 'X86int form? (pairify assign-home)))
;;------------------------------------------------------------------------------------

;;X86raw
;;------------------------------------------------------------------------------------
(define (install-X86raw)
  (install-x86-instruction-block)

  (define form?
    (opt/c
     (cons/c
      'program
      (and/c (listof (get-contract 'x86-instruction-block))
             (lambda (ls)
               (match ls
                 ((list-no-order (list 'main _) (list 'start _) (list 'conclusion _)) #t)
                 (_ #f)))))))
  
  (define (block->string b) (apply-generic 'block->string 'x86-instruction-block b))
  
  (define (make-text form)
    (string-append* (cons (format ".global ~amain\n" (if (eq? (system-type 'os) 'macosx) "_" "")) (map block->string (cdr form)))))
  
  (apply install 'X86raw form? (pairify make-text)))
;;------------------------------------------------------------------------------------

;;All
;;------------------------------------------------------------------------------------
(define (install-All)
  (install 'Lvar-compiler (listof (list/c (and/c tag? installed?) tag? boolean?))
           (cons 'make-Lvar-compiler
                 (lambda (l)
                   (lambda (i (f #t))
                     (foldl
                      (lambda (p i) (if (or f (caddr p)) (apply-generic (cadr p) (car p) i) i))
                      i l)))))
  (install-Lvar)
  (install-Lvar_mon)
  (install-Cvar)
  (install-X86int)
  (install-X86raw)
  
  (apply-generic 'make-Lvar-compiler 'Lvar-compiler
                 (list (list 'Lvar 'uniquify #t)
                       (list 'Lvar 'remove-complex-operands #t)
                       (list 'Lvar_mon 'explicate-control #t)
                       (list 'Cvar 'partial-evaluate #f)
                       (list 'Cvar 'select-instructions #t)
                       (list 'X86int 'assign-home #t)
                       (list 'X86raw 'make-text #t))))
;;------------------------------------------------------------------------------------
