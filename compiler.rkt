#lang racket/base
(require racket/contract racket/match racket/generator racket/dict racket/string racket/set racket/list
         graph
         "pkg.rkt" "instruction.rkt"
         (for-syntax racket/base))
(provide install-Lvar install-Lvar_mon install-Cvar install-X86raw install-All)

(define (install-language name contract interpreter . passes)
  (apply install name contract (cons 'interpret interpreter) passes))

(define-syntax-rule (pairify id ...) (list (cons 'id id) ...))

(define (n:gensym s)
  (string->symbol (symbol->string (gensym s))))

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
  
  #; (-> Lvar |restricted Lvar|)
  (define (uniquify form (table (hasheq)))
    (define (reference v t)
      (hash-ref t v (lambda () (raise (make-exn:fail:contract:variable v "not yet defined" (current-continuation-marks))))))
    (match form
      ((list 'let (list (list v e)) f)
       (define-values (nv nt)
         (let ((new-v (n:gensym v)))
           (values new-v (hash-set table v new-v))))
       (list 'let (list (list nv (uniquify e table))) (uniquify f nt)))
      (exp (cond ((symbol? exp) (reference exp table))
                 ((primitive? exp) exp)
                 (else (cons (car exp) (map (lambda (s) (uniquify s table)) (cdr exp))))))))
  #; (-> Lvar Lvar_mon)
  (define (remove-complex-operands form)
    (if (mon? form)
        form
        (match form
          ((list 'let (list (list v e)) f)
           (list 'let (list (list v (remove-complex-operands e)))
                 (remove-complex-operands f)))
          ((list op sub ...)
           (define-values (st dy)
             (for/fold ((s null) (d null)) ((e (in-list sub)))
               (let ((r (remove-complex-operands e)))
                 (cond ((primitive? r) (values (cons r s) d))
                       (else
                        (define ns (n:gensym 'tmp))
                        (values (cons ns s) (cons (cons ns r) d)))))))
           (foldl (lambda (pair base) (list 'let (list (list (car pair) (cdr pair))) base))
                  (cons op (reverse st)) dy)))))

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
;;locations
(struct register (name) #:transparent)
(define caller-saved-registers (map register '(rax rcx rdx rsi rdi r8 r9 r10 r11)))
(define callee-saved-registers (map register '(rsp rbp rbx r12 r13 r14 r15)))
(define argument-passing-registers (map register '(rdi rsi rdx rcx r8 r9)))

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
  ;; This is an optional optimization.
  ;; Only addition, negation and subtraction are covered.
  (define (partial-evaluate form)
    ;;assoc: (cons/c <var> <value>)
    ;;<var>: symbol?
    ;;<value>: (list/c <static> <dynamic>)
    ;;<static>: fixnum?
    ;;<dynamic>: (or/c #f <var> (list/c '+ <var> <var>) (list/c '- <var> <var>) (list/c '- <var>) (list/c <operator> (listof <value>)))
    ;;<operator>: symbol?
    (define sequence
      (match form
        ((list 'program (list 'start statements))
         (define (reference d v) (dict-ref d v (lambda () (make-exn:fail:contract:variable v "not yet defined" (current-continuation-marks)))))
         (define (trace d s)
           (if (fixnum? s)
               (values s #f)
               (let loop ((f #f) (s s))
                 (define v (reference d s))
                 (cond
                   ((not (cadr v)) (values (car v) #f)) ;;this branch should always be reached when `loop` is first called due to infectivity
                   ((symbol? (cadr v)) (if f (loop f (cadr v)) (values (car v) (loop #t (cadr v)))))
                   (else (if f s (values (car v) s)))))))
         (for/fold ((dict null))
                   ((st (in-list statements)))
           (define-syntax-rule (handle h p1 p2)
             (let-values (((n1 d1) (trace dict p1))
                          ((n2 d2) (trace dict p2)))
               (list (h n1 n2)
                     (cond ((and d1 d2) (list 'h d1 d2))
                           (d1)
                           (d2 (if (eq? 'h '+) d2 (list '- d2)))
                           (else #f)))))
           (cons
            (cons (if (tail? st) #f (cadr st))
                  (match (if (tail? st) (cadr st) (caddr st))
                    ((list '+ p1 p2) (handle + p1 p2))
                    ((list '- p1 p2) (handle - p1 p2))
                    ((list '- p) (handle - 0 p))
                    ;;for extensibility
                    ((list op arg ...) (list 0 (list op (map (lambda (a) (handle + 0 a)) arg))))
                    (p (handle + 0 p))))
            dict)))))
    (define (merge n a make-continuation else-proc)
      (let/cc ret
        (list
         (make-continuation
          (let loop ((n n) (a a))
            (cond ((not a) n)
                  ;;for extensibility
                  ;;In this case, the last branch will never be reached during recursive calls to `loop`, and `n` will always be zero.
                  (((list/c symbol? list?) a)
                   (let-values (((f c)
                                 (for/fold ((final null) (complex null))
                                           ((a (in-list (cadr a))))
                                   (define result (loop (car a) (cadr a)))
                                   (cond ((primitive? result) (values (cons result final) complex))
                                         (else
                                          (define ns (n:gensym 'arg))
                                          (values (cons ns final) (cons (list 'define ns result) complex)))))))
                     (ret (reverse (cons (make-continuation (cons (car a) (reverse f))) c)))))
                  ((zero? n) a)
                  ((symbol? a) (list '+ n a))
                  (((list/c '- symbol?) a) (cons '- (cons n (cdr a))))
                  (else (else-proc n a ret make-continuation))))))))
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
                         (merge n a (lambda (e) (list 'return e))
                                (lambda (n a ret make-continuation)
                                  (define ns (n:gensym 'ret))
                                  (ret (list (list 'define ns a)
                                             (make-continuation (list '+ ns n)))))))
                        ;;assignment
                        ((list var _ expr)
                         (cond ((or (not expr) (symbol? expr)) null)
                               (((list/c symbol? list?) expr) (merge 0 expr (lambda (e) (list 'define var e)) void))
                               (else (list (list 'define var expr))))))
                      re))
                   null
                   (reverse sequence)))))))
  #; (-> Cvar X86int)
  ;; without register allocation
  (define (select-instructions form)
    (define (format-instruction template . args)
      (apply apply-generic 'format-instruction (tag 'x86-instruction-template template) args))
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
       (define stack-size (* 16 (ceiling (/ (- (+ 8 (gen))) 16))))
       (list 'program (pairify stack-size) block))))
  #; (-> Cvar Cvar_conflicts)
  ;; Including `uncover-live` pass and `build-interference` pass
  ;; The `live` argument is used to pass live-after sets when the flow jumps from the `start` block to another block.
  ;; The items in the set can be compound objects so that lists used as sets and hash sets built with `set` are recommended.
  ;; Hash sets built with `mutable-set` are also allowed, but not preferred.
  (define (find-conflicts form (live (set)))
    (define (left-hand st)
      (match st
        ((list 'define var _) var)
        ((list 'return _) (register 'rax))))
    (define (right-hand st)
      (match st
        ((list 'define _ e) e)
        ((list 'return e) e)))

    (define (W st)
      (define base (left-hand st))
      (define registers
        (let ((r (right-hand st)))
          (if (or (primitive? r) (eq? (car r) '+) (eq? (car r) '-)) null caller-saved-registers)))
      (list->set (cons base registers)))
    (define (R st)
      (define base (right-hand st))
      (cond ((symbol? base) (set base))
            ((primitive? base) (set))
            (else
             (define registers
               (if (or (eq? (car base) '+) (eq? (car base) '-))
                   null (take argument-passing-registers (min 6 (length (cdr base))))))
             (list->set (append registers (filter symbol? (cdr base)))))))
    
    (define (uncover-live sts)
      (reverse
       (cdr
        (for/fold ((ac (list live)))
                  ((st (in-list (reverse sts))))
          (define write-set (W st))
          (define read-set (R st))
          (cons (set-union (set-subtract (car ac) write-set) read-set) (cons (list (car ac) write-set read-set) (cdr ac)))))))

    (define (build-interference ls)
      (undirected-graph
       (for/fold ((s null)) ((l (in-list ls)))
         (match l
           ((list live write read)
            (for/fold ((s s)) ((wloc (in-set write)))
              (for/fold ((s s)) ((lloc (in-set live)))
                (cond ((equal? wloc lloc) s) (else (set-add s (list wloc lloc)))))))))))
    
    (match form
      ((list 'program (list 'start statements))
       (define conflicts (build-interference (uncover-live statements)))
       (list 'program (pairify conflicts) (list 'start statements)))))
  
  (apply install-language 'Cvar Cvar? Cvar-interpret (pairify partial-evaluate select-instructions find-conflicts)))
;;------------------------------------------------------------------------------------

;;X86int
;;------------------------------------------------------------------------------------
(define (install-X86int)
  (install-x86-instruction)

  (define form? (opt/c (list/c 'program (list/c (cons/c 'stack-size fixnum?)) (list/c 'start (listof (get-contract 'x86-instruction))))))

  #; (-> X86int X86raw)
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
  
  (define (block->string b) (apply-generic 'block->string (tag 'x86-instruction-block b)))

  #; (-> X86raw string?)
  (define (make-text form)
    (string-append* (cons (format ".global ~a\n" (resolve-label 'main)) (map block->string (cdr form)))))
  
  (apply install 'X86raw form? (pairify make-text)))
;;------------------------------------------------------------------------------------

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
                                    (list 'X86int 'assign-home #t)
                                    (list 'X86raw 'make-text #t)))))
            'Lvar2
            (lambda ()
              (install-Lvar)
              (install-Lvar_mon)
              (install-Cvar)

              (apply-generic 'make-compiler
                             (tag
                              'compiler
                              (list (list 'Lvar 'uniquify #t)
                                    (list 'Lvar 'remove-complex-operands #t)
                                    (list 'Lvar_mon 'explicate-control #t)
                                    (list 'Cvar 'partial-evaluate #f)
                                    (list 'Cvar 'find-conflicts #t (set (register 'rsp) (register 'rax)))
                                    ))))))
  
  ((hash-ref table name)))
;;------------------------------------------------------------------------------------
