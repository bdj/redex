#lang racket
(require redex)

(provide (all-defined-out))

(define-language
  compiled
  [program (mod ...)]
  [mod (module id (req ...) (code ...))]
  [code (phase (expr ...))]
  [req (require id @ phase)]
  [expr var
        val
        (+ expr expr)
        (set! var expr)]
  [val number
       (quote id @ phase)]
  [var (id id)]
  [id variable-not-otherwise-mentioned]
  [phase number])

(define-extended-language
  compiled/eval compiled
  [E hole
     (+ E expr)
     (+ val E)
     (set! var E)]
  [σ ([var val] ...)]
  [state (program / (inst ...) / (inst ...))]
  [inst (id phase)]
  [st (σ / state)])

(define -->/ce
  (reduction-relation
   compiled/eval
   #:domain st
   [--> (σ / ((mod_0 ... (module id_0 ((require id_new @ phase_new) req ...) (code ...)) mod_n ...) / ((id_0 phase_0) inst_n ...) / (inst_d ...)))
        (σ / ((mod_0 ... (module id_0 (req ...) (code ...)) mod_n ...) / ((id_new ,(+ (term phase_new) (term phase_0))) (id_0 phase_0) inst_n ...) / (inst_d ...)))
        "module require"]
   [--> (σ / (in-hole ((mod_0 ... (module id_0 () (code_0 ... (phase (E expr ...)) code_n ...)) mod_n ...) / ((id_0 phase_0) inst_n ...) / (inst_d ...)) var))
        (σ / (in-hole ((mod_0 ... (module id_0 () (code_0 ... (phase (E expr ...)) code_n ...)) mod_n ...) / ((id_0 phase_0) inst_n ...) / (inst_d ...)) val))
        (side-condition (zero? (+ (term phase) (term phase_0))))
        (where val (lookup σ var))
        "var ref"]
   [--> (σ / (in-hole ((mod_0 ... (module id_0 () (code_0 ... (phase (E expr ...)) code_n ...)) mod_n ...) / ((id_0 phase_0) inst_n ...) / (inst_d ...)) (+ number_0 number_1)))
        (σ / (in-hole ((mod_0 ... (module id_0 () (code_0 ... (phase (E expr ...)) code_n ...)) mod_n ...) / ((id_0 phase_0) inst_n ...) / (inst_d ...)) ,(+ (term number_0) (term number_1))))
        (side-condition (zero? (+ (term phase) (term phase_0))))
        "add"]
   [--> (σ_0 / (in-hole ((mod_0 ... (module id_0 () (code_0 ... (phase (E expr ...)) code_n ...)) mod_n ...) / ((id_0 phase_0) inst_n ...) / (inst_d ...)) (set! var val)))
        (σ_1 / (in-hole ((mod_0 ... (module id_0 () (code_0 ... (phase (E expr ...)) code_n ...)) mod_n ...) / ((id_0 phase_0) inst_n ...) / (inst_d ...)) val))
        (side-condition (zero? (+ (term phase) (term phase_0))))
        (where σ_1 (assign σ_0 var val))
        "set!"]
   [--> (σ / ((mod_0 ... (module id_0 () (code_0 ... (phase (val expr ...)) code_n ...)) mod_n ...) / ((id_0 phase_0) inst_n ...) / (inst_d ...)))
        (σ / ((mod_0 ... (module id_0 () (code_0 ... (phase (expr ...)) code_n ...)) mod_n ...) / ((id_0 phase_0) inst_n ...) / (inst_d ...)))
        (side-condition (zero? (+ (term phase) (term phase_0))))
        "expression done"]
   [--> (σ / ((mod_0 ... (module id_0 () (code_0 ... (phase ()) code_n ...)) mod_n ...) / ((id_0 phase_0) inst_n ...) / (inst_d ...)))
        (σ / ((mod_0 ... mod_n ...) / (inst_n ...) / ((id_0 phase_0) inst_d ...)))
        (side-condition (zero? (+ (term phase) (term phase_0))))
        "module done"]
   [--> (σ / ((mod ...) / (inst_0 inst_n ...) / (inst_d0 ... inst_0 inst_dn ...)))
        (σ / ((mod ...) / (inst_n ...) / (inst_d0 ... inst_0 inst_dn ...)))
        "module done already"]))

(define-metafunction compiled/eval
  lookup : σ var -> val
  [(lookup ([var_0 val_0] ... [var val] [var_n val_n] ...) var)
   val]
  [(lookup σ var)
   ,(error 'lookup "unbound variable reference: ~a" (term var))])

(define-metafunction compiled/eval
  assign : σ var val -> σ
  [(assign ([var_0 val_0] ... [var val_old] [var_n val_n] ...) var val_new)
   ([var_0 val_0] ... [var val_new] [var_n val_n] ...)]
  [(assign ([var val] ...) var_new val_new)
   ([var val] ... [var_new val_new])])


;; run : compiled id -> [var -> val]
;; many modules to one mapping as modules are instantiated and run
(define (run prog main)
  #;(traces -->/ce (term (() / (,prog / ((,main 0)) / ()))))
  (match (apply-reduction-relation* -->/ce (term (() / (,prog / ((,main 0)) / ()))))
    [(list (list σ '/ (list prog* '/ (list) '/ done)))
     σ]
    [(and (list one two ...) ans)
     (error 'run "nondeterministic: ~a" ans)]
    [else
     (error 'run "leftover modules")]))

(define (compile/run prog main)
  (run (term (compile ,prog)) main))

(define-extended-language
  expanded-core compiled
  [mod (module id (req ...) (def ...) (expr ...))]
  [def (define id @ phase as expr)]
  [var id])

(define-extended-language
  expanded expanded-core
  [var ....
       (id id)])

(define (re-balance small big)
  (for/list ([id_m (in-list small)]
             [id_ds (in-list big)])
    (map (λ _ id_m) id_ds)))

;; compile : expanded -> compiled
;; Many modules to many modules with resolved refs
(define-metafunction expanded
  compile : program -> any
  [(compile (name modules ((module id_m (req ...) ((define id_d @ phase_d as expr_d) ...) (expr_m ...)) ...)))
   ((module id_m (req ...) (compile-code id_m 
                                         (id_d ...) 
                                         (phase_d ...)
                                         ((resolve-ref id_md phase_d modules expr_d) ...) 
                                         ((resolve-ref id_mm 0 modules expr_m) ...)))
    ...)
   (where ((id_md ...) ...)
          ,(re-balance (term (id_m ...)) (term ((id_d ...) ...))))
   (where ((id_mm ...) ...)
          ,(re-balance (term (id_m ...)) (term ((expr_m ...) ...))))])

(define-metafunction expanded
  compile-code : id (id ...) (phase ...) (expr ...) (expr ...) -> any
  [(compile-code id_m (id_d ...) (phase_d ...) (expr_d ...) (expr_m ...))
   ,(compile-code* (term id_m) (term (id_d ...)) (term (phase_d ...)) (term (expr_d ...)) (term (expr_m ...)))])

(define (compile-code* m-id def-ids def-phases def-exprs m-exprs)
  (define (snoc l v)
    (append l (list v)))
  (define phase->exprs
    (for/fold ([h (hasheq)])
      ([id (in-list def-ids)]
       [phase (in-list def-phases)]
       [expr (in-list def-exprs)])
      (hash-update h phase (λ (exprs) (snoc exprs (term (set! (,m-id ,id) ,expr)))) (λ () empty))))
  (define phase->exprs*
    (hash-update phase->exprs 0 (λ (exprs) (append exprs m-exprs)) (λ () empty)))
  (sort (for/list ([(phase exprs) (in-hash phase->exprs*)])
          (list phase exprs))
        <
        #:key car))

(module+ test
  (test-equal (term (compile ((module foo () () ())))) 
              (term ((module foo () ((0 ()))))))
  (test-equal (term (compile ((module foo () ((define x @ 0 as 5)) ()))))
              (term ((module foo () ((0 ((set! (foo x) 5))))))))
  (test-equal (term (compile ((module foo () ((define x @ 0 as 5)) ((set! x 4))))))
              (term ((module foo () ((0 ((set! (foo x) 5) (set! (foo x) 4))))))))
  (test-equal (term (compile ((module foo ((require bar @ 1)) ((define x @ 1 as (+ y 8))) ((set! x 3)))
                              (module bar () ((define x @ -1 as 9) (define y @ 0 as 4)) ()))))
              (term ((module foo ((require bar @ 1)) ((0 ((set! (bar x) 3))) (1 ((set! (foo x) (+ (bar y) 8))))))
                     (module bar () ((-1 ((set! (bar x) 9))) (0 ((set! (bar y) 4)))))))))


(define-metafunction expanded
  resolve-ref : id phase (mod ...) expr -> expr
  ;; defined in current module 
  [(resolve-ref id phase (mod ...) (+ expr_0 expr_1))
   (+ (resolve-ref id phase (mod ...) expr_0) (resolve-ref id phase (mod ...) expr_1))]
  [(resolve-ref id phase (mod ...) val)
   val]
  [(resolve-ref id phase (mod ...) (id_m id_d))
   (id_m id_d)]
  [(resolve-ref id_m phase (mod_0 ... (module id_m (req ...) (def_0 ... (define id_d @ phase as expr_d) def_n ...) (expr_m ...)) mod_n ...) id_d)
   (id_m id_d)]
  [(resolve-ref id_m phase (mod_0 ... (module id_m (req ...) (def_0 ... (define id_d @ phase as expr_d) def_n ...) (expr_m ...)) mod_n ...) (set! id_d expr))
   (set! (id_m id_d) expr)]
  ;; defined in required module
  [(resolve-ref id_m phase (mod_0 ... 
                            (module id_m (req_0 ... (require id_r @ phase_r) req_n ...) (def_m ...) (expr_m ...)) 
                            mod_i ... 
                            (module id_r (req_r ...) (def_r ...) (expr_r ...))
                            mod_n ...) expr)
   (resolve-ref id_r ,(- (term phase) (term phase_r)) (mod_0 ... mod_i ... (module id_r (req_r ...) (def_r ...) (expr_r ...)) mod_n ...) expr)]
  [(resolve-ref id_m phase (mod_0 ... 
                            (module id_r (req_r ...) (def_r ...) (expr_r ...))
                            mod_i ... 
                            (module id_m (req_0 ... (require id_r @ phase_r) req_n ...) (def_m ...) (expr_m ...)) 
                            mod_n ...) expr)
   (resolve-ref id_r ,(- (term phase) (term phase_r)) (mod_0 ... (module id_r (req_r ...) (def_r ...) (expr_r ...)) mod_i ... mod_n ...) expr)]
  
  [(resolve-ref id phase (mod ...) expr)
   ,(error 'resolve-ref "cannot resolve reference ~a" (term expr))])

(module+ test
  (test-equal (term (resolve-ref foo 0 ((module foo () ((define x @ 0 as 5)) ())) x)) 
              (term (foo x)))
  (test-equal (term (resolve-ref foo 0 ((module foo () ((define x @ 0 as 5)) ())) (set! x 6))) 
              (term (set! (foo x) 6)))
  (test-equal (term (resolve-ref foo 0 ((module foo ((require bar @ 0)) () ())
                                        (module bar () ((define y @ 0 as 4)) ())) y)) 
              (term (bar y)))
  (test-equal (term (resolve-ref foo 0 ((module bar () ((define y @ 0 as 4)) ())
                                        (module foo ((require bar @ 0)) () ())) y)) 
              (term (bar y)))
  (test-equal (term (resolve-ref foo 0 ((module foo ((require bar @ 1)) () ())
                                        (module bar () ((define y @ -1 as 4)) ())) y)) 
              (term (bar y)))
  (test-equal (term (resolve-ref foo 0 ((module foo ((require bar @ 1)) () ())
                                        (module bar ((require baz @ 1)) () ())
                                        (module baz () ((define z @ -2 as 3)) ())) z))
              (term (baz z)))
  
  (test-equal (term (resolve-ref foo 0 ((module foo () ((define x @ 0 as 1)) ())) (+ x x)))
              (term (+ (foo x) (foo x)))))


;; demod : expanded id -> compiled
;; many modules to one module with resolve refs


(module+ test
  ;; module with no requires and only phase 0 code
  (test-equal (term (demod foo () ((module foo () ((0 ((set! (foo x) 5))))))))
              (term ((module foo () ((0 ((set! (foo x) 5))))))))
  ;; module with no requires and multiple phases
  (test-equal (term (demod foo () ((module foo () ((-1 ((set! (foo y) 6))) (0 ((set! (foo x) 3))))))))
              (term ((module foo () ((0 ((set! (foo x) 3))))))))
  ;; mulitple modules, but main has no requires
  (test-equal (term (demod foo () ((module foo () ((0 ((set! (foo x) 5)))))
                                   (module bar () ((0 ((set! (bar y) 3))))))))
              (term ((module foo () ((0 ((set! (foo x) 5))))))))
  ;; module with phase 0 require
  (test-equal (term (demod foo () ((module foo ((require bar @ 0)) ((0 ((set! (foo x) 5)))))
                                   (module bar () ((0 ((set! (bar y) 4) (set! (bar y) 2))))))))
              (term ((module foo () ((0 ((set! (bar y) 4) (set! (bar y) 2) (set! (foo x) 5))))))))
  ;; module with phase 1 require and phase -1 def
  (test-equal (term (demod foo () ((module foo ((require bar @ 1)) ((0 ((set! (foo x) 5) (set! (bar z) 3)))))
                                   (module bar () ((-1 ((set! (bar z) 8))) (0 ((set! (bar y) 3) (set! (bar y) 6))))))))
              (term ((module foo () ((0 ((set! (bar z) 8) (set! (foo x) 5) (set! (bar z) 3)))))))) 
  
  ;; required module without code
  (test-equal (term (demod foo () ((module foo ((require bar @ 1)) ((0 ((set! (foo x) 5)))))
                                   (module bar () ((0 ((set! (bar y) 4))))))))
              (term ((module foo () ((0 ((set! (foo x) 5))))))))
  ;; multiple
  )

;; todo: use plus for the phase and zero? to mirror eval

(define-metafunction compiled
  demod : id ((id phase) ...) program -> program
  ;; no requires left, return phase 0 code only
  [(demod id () (mod_0 ... (module id () (code_0 ... (0 (expr ...)) code_n ...)) mod_n ...))
   ((module id () ((0 (expr ...)))))]
  ;; require with code
  [(demod id () ((module id ((require id_r @ phase_r) req_m ...) (code_m0 ... (0 (expr_m ...)) code_mn ...))
                 (module id_r (req_r ...) (code_r0 ... (phase_nr (expr_r ...)) code_rn ...))
                   mod_n ...))
   (demod id ((id_r ,(- (term phase_r))))
          ((module id (req_m ...) (code_m0 ... (0 (expr_r ... expr_m ...)) code_mn ...))
           (module id_r (req_r ...) (code_r0 ... (phase_nr (expr_r ...)) code_rn ...))
           mod_n ...))
   (where phase_nr ,(- (term phase_r)))]
  ;; require without code
  [(demod id () ((module id ((require id_r @ phase_r) req_m ...) (code_m ...))
                 (module id_r (req_r ...) (code_r ...))
                 mod_n ...))
   (demod id ((id_r ,(- (term phase_r))))
          ((module id (req_m ...) (code_m ...))
           (module id_r (req_r ...) (code_r ...))
           mod_n ...))]
  ;; require of require with code
  [(demod id ((id_c phase_c) (id_n phase_n) ...) 
          ((module id (req_m ...) (code_m0 ... (0 (expr_m ...)) code_mn ...))
           (module id_c ((require id_r @ phase_r) req_c ...) (code_c ...))
           (module id_r (req_r ...) (code_r0 ... (phase_c (expr_r ...)) code_rn ...))
           mod_n ...))
   (demod id ((id_r ,(- (term phase_c) (term phase_r))) (id_c phase_c) (id_n phase_n) ...)
          ((module id (req_m ...) (code_m0 ... (0 (expr_r ... expr_m ...)) code_mn ...))
           (module id_c (req_c ...) (code_c ...))
           (module id_r (req_r ...) (code_r0 ... (phase_c (expr_r ...)) code_rn ...))
           mod_n ...))]
  ;; require of require without code
  [(demod id ((id_c phase_c) (id_n phase_n) ...)
          ((module id (req_m ...) (code_m ...))
           (module id_c ((require id_r @ phase_r) req_c ...) (code_c ...))
           (module id_r (req_r ...) (code_r ...))
           mod_n ...))
   (demod id ((id_r ,(- (term phase_c) (term phase_r))) (id_c phase_c) (id_n phase_n) ...)
          ((module id (req_m ...) (code_m ...))
           (module id_c (req_c ...) (code_c ...))
           (module id_r (req_r ...) (code_r ...))
           mod_n ...))]
  ;; no more require of requires
  [(demod id ((id_c phase_c) (id_n phase_n) ...) 
          ((module id (req_m ...) (code_m ...))
           (module id_c () (code_c ...))
           mod_n ...))
   (demod id ((id_n phase_n) ...)
          ((module id (req_m ...) (code_m ...))
           (module id_c () (code_c ...))
           mod_n ...))]
  
  ;; rearrange stuff
  [(demod id () (mod_0 ... (module id (req ...) (code ...)) mod_n ...))
   (demod id () ((module id (req ...) (code ...)) mod_0 ... mod_n ...))]
  [(demod id () ((module id ((require id_r @ phase_r) req_m ...) (code_m ...)) mod_i ... (module id_r (req_r ...) (code_r ...)) mod_n ...))
   (demod id () ((module id ((require id_r @ phase_r) req_m ...) (code_m ...)) (module id_r (req_r ...) (code_r ...)) mod_i ... mod_n ...))]
  [(demod id ((id_c phase_c) (id_n phase_n) ...)
          ((module id (req_m ...) (code_m ...))
           mod_i ...
           (module id_c (req_c ...) (code_c ...))
           mod_n ...))
   (demod id ((id_c phase_c) (id_n phase_n) ...)
          ((module id (req_m ...) (code_m ...))
           (module id_c (req_c ...) (code_c ...))
           mod_i ...
           mod_n ...))]
  [(demod id ((id_c phase_c) (id_n phase_n) ...)
          ((module id (req_m ...) (code_m ...))
           (module id_c ((require id_r @ phase_r) req_c ...) (code_c ...))
           mod_i ...
           (module id_r (req_r ...) (code_r ...))
           mod_n ...))
   (demod id ((id_c phase_c) (id_n phase_n) ...)
          ((module id (req_m ...) (code_m ...))
           (module id_c ((require id_r @ phase_r) req_c ...) (code_c ...))
           (module id_r (req_r ...) (code_r ...))
           mod_i ...
           mod_n ...))])
  



;; todo: change (id id) to locations

(module+ test
  (test-results))

(define-extended-language
  source expanded-core
  [var ....
       (ref id @ phase)])
#|
forall e:expanded, id:id,
 run(compile(e),id) = run(demod(e,id),id)
|#