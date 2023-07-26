#lang racket/base
(require racket/contract racket/match racket/dict racket/string racket/set racket/list
         graph
         "pkg.rkt" "selector.rkt" "instruction.rkt" "support/priority_queue.rkt"
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
;;registers
;;They are all interned strings.
(define caller-saved-registers '("rax" "rcx" "rdx" "rsi" "rdi" "r8" "r9" "r10" "r11"))
(define callee-saved-registers '("rsp" "rbp" "rbx" "r12" "r13" "r14" "r15"))
(define argument-passing-registers '("rdi" "rsi" "rdx" "rcx" "r8" "r9"))

;;common contracts
(define assign? (list/c 'define symbol? atomic?))
(define tail? (list/c 'return atomic?))

(define (install-Cvar)
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
         (define (trace d p)
           (if (fixnum? p)
               (values p #f)
               (let ((v (reference d p)))
                 (values (car v) (if (or (not (cadr v)) (symbol? (cadr v))) (cadr v) p)))))
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
    (match form
      ((list 'program (list 'start (list (list 'define var expr) ... (list 'return last-expr))))
       (let* ((location-table
               (make-hasheq
                (for/list ((v (in-list var))
                           (n (in-naturals 1)))
                  (cons v n))))
              (stack-size (* 8 (hash-count location-table)))
              (callee-saved-registers-in-use null)
              (number->location (lambda (n) (if (zero? n) "rax" (cons (* -8 n) "rbp"))))
              (variable->number
               (lambda (v) (hash-ref location-table v (lambda () (raise (make-exn:fail:contract:variable v "There is no location allocated for this variable" (current-continuation-marks)))))))
              (handle (apply-generic 'make-instruction-selector (tag 'selector (list number->location variable->number 0)))))
         (list 'program
               (pairify stack-size callee-saved-registers-in-use)
               (list 'start
                     (append
                      (apply append
                             (map (lambda (v e) (handle v e)) var expr))
                      (handle 0 last-expr))))))))
  #; (-> Cvar Cvar_conflicts)
  ;; Including `uncover-live` pass and `build-interference` pass
  ;; The `live` argument is used to pass live-after sets when the flow jumps from the `start` block to another block.
  ;; So it is much more secure to use lists as sets or build hash sets with `set`, using `equal?` to compare elements.
  ;; Hash sets built with `mutable-set` are also allowed, but not preferred.
  (define (find-conflicts form (live (set)))
    (define (left-hand st)
      (match st
        ((list 'define var _) var)
        ((list 'return _) "rax")))
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

;;Cvar_conflicts
;;------------------------------------------------------------------------------------
(define (install-Cvar_conflicts)
  (define Cvar_conflicts?
    (list/c 'program (list/c (cons/c 'conflicts graph?))
            (list/c 'start (*list/c assign? tail?))))

  #; (-> Cvar_conflicts X86int)
  (define (allocate-registers form)
    (match form
      ((list 'program (list (cons 'conflicts graph)) (list 'start statements))
       ;;All keys are interned.
       (define-syntax-rule (make-mapping (int reg) ...) (values (hasheq (~@ int reg) ...) (hasheq (~@ reg int) ...)))
       (define-values (number->register register->number)
         (make-mapping
          (-5 "r15") (-4 "r11") (-3 "rbp") (-2 "rsp") (-1 "rax")
          (0 "rcx") (1 "rdx") (2 "rsi") (3 "rdi") (4 "r8") (5 "r9") (6 "r10") (7 "rbx") (8 "r12") (9 "r13") (10 "r14")))
       
       (define-values (registers identifiers) (partition register? (get-vertices graph)))
       
       (define saturation-table (make-hasheq))
       (define exclusion-table (make-hasheq))
       (define handles-mapping (make-hasheq))
       (define location-table (make-hasheq))
       
       (define (variable-saturation id)
         (hash-ref saturation-table id))
       (define (update id num)
         (define new-set (set-add (hash-ref exclusion-table id) num))
         (hash-set! exclusion-table id new-set)
         (hash-set! saturation-table id (set-count new-set)))
       (define (count id)
         (define rs (filter (lambda (reg) (has-edge? graph reg id)) registers))
         (define new-set (list->seteq (map (lambda (reg) (hash-ref register->number reg)) rs)))
         (hash-set! saturation-table id (set-count new-set))
         (hash-set! exclusion-table id new-set))

       (define pqueue
         (make-pqueue
          (lambda (var1 var2)
            (> (variable-saturation var1) (variable-saturation var2)))))
       (map (lambda (id) (count id) (hash-set! handles-mapping id (pqueue-push! pqueue id))) identifiers)
       
       (define (color var)
         (define exclusion (hash-ref exclusion-table var))
         (define num
           (let/cc ret
             (for ((n (in-naturals)))
               (cond ((not (set-member? exclusion n)) (ret n))))))
         (for ((n (in-neighbors graph var)))
           (cond ((not (register? n))
                  (update n num)
                  (pqueue-decrease-key! pqueue (hash-ref handles-mapping n)))))
         num)

       (let loop ((c (pqueue-count pqueue)))
         (cond ((not (zero? c))
                (let* ((v (pqueue-pop! pqueue)))
                  (hash-set! location-table v (color v))
                  (loop (sub1 c))))))

       (define callee-saved-registers-in-use
         (set->list (list->seteq (map (lambda (int) (hash-ref number->register int)) (filter (lambda (int) (and (>= int 7) (<= int 10))) (hash-values location-table))))))
       (define stack-size
         (let ((vals (hash-values location-table)))
           (if (null? vals) 0
               (let ((m (argmax values vals)))
                 (if (> m 10) (* 8 (- m 10)) 0)))))

       (define base (length callee-saved-registers-in-use))
       
       (define (number->location num)
         (if (> num 10) (list '~a (cons (* -8 (+ base (- num 10))) "rbp")) (list '~r (hash-ref number->register num))))
       (define (variable->number var)
         (hash-ref location-table var (lambda () (raise (make-exn:fail:contract:variable var "There is no location allocated for this variable" (current-continuation-marks))))))
       
       (define handle (apply-generic 'make-instruction-selector (tag 'selector (list number->location variable->number -1))))
                     
       (list 'program (pairify stack-size callee-saved-registers-in-use)
             (list 'start
                   (apply append (map (lambda (st) (match st
                                                     ((list 'define var expr) (handle var expr))
                                                     ((list 'return expr) (handle -1 expr))))
                                      statements)))))))
  
  (apply install 'Cvar_conflicts Cvar_conflicts? (pairify allocate-registers)))
;;------------------------------------------------------------------------------------

;;X86int
;;------------------------------------------------------------------------------------
(define (install-X86int)
  (define form? (opt/c (list/c 'program
                               (and/c list? (lambda (l)
                                              (match l
                                                ((list-no-order (cons 'stack-size f) (cons 'callee-saved-registers-in-use sl))
                                                 (and (fixnum? f) ((listof register?) sl)))
                                                (_ #f))))
                               (list/c 'start (listof (get-contract 'x86-instruction))))))

  #; (-> X86int X86int)
  (define (patch-instructions form)
    (match form
      ((list 'program dict (list 'start statements))
       (list 'program
             dict
             (list 'start
                   (apply append
                          (map (lambda (st)
                                 (match st
                                   ((list op arg1 arg2)
                                    (if (and (address? arg1) (address? arg2))
                                        (list (list 'movq arg1 "rax")
                                              (list op "rax" arg2))
                                        (list st)))
                                   (_ (list st))))
                               statements)))))))

  #; (-> X86int X86raw)
  (define (assign-home form)
    (match form
      ((list 'program (list-no-order (cons 'stack-size stack-size) (cons 'callee-saved-registers-in-use callee-saved-registers-in-use))
             (list 'start statements))
       (define save-space (* 8 (length callee-saved-registers-in-use)))
       (define offset (- (* 16 (ceiling (/ (+ save-space stack-size) 16))) save-space))
       (define align? (not (zero? offset)))
       (list
        'program
        (list 'start (append statements (list '(jmp (~l conclusion)))))
        (list
         'main
         (append
          (if align?
              '((pushq "rbp")
                (movq "rsp" "rbp"))
              null)
          (map (lambda (r) (list 'pushq r)) callee-saved-registers-in-use)
          (if align? (list (list 'subq offset "rsp")) null)
          (list '(jmp (~l start)))))
        (list
         'conclusion
         (append (if align? (list (list 'addq offset "rsp")) null)
                 (map (lambda (r) (list 'popq r)) (reverse callee-saved-registers-in-use))
                 (if align? '((popq "rbp")) null)
                 (list '(retq))))))))

  (apply install 'X86int form? (pairify assign-home patch-instructions)))
;;------------------------------------------------------------------------------------

;;X86raw
;;------------------------------------------------------------------------------------
(define (install-X86raw)
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
                                    (list 'Cvar 'find-conflicts #t (set "rsp" "rax"))
                                    (list 'Cvar_conflicts 'allocate-registers #t)
                                    (list 'X86int 'patch-instructions #t)
                                    (list 'X86int 'assign-home #t)
                                    (list 'X86raw 'make-text #t)))))))
  
  ((hash-ref table name)))
;;------------------------------------------------------------------------------------
