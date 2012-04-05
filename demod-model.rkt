#lang racket
(require redex)

(define-language
  compiled
  [program (mod ...)]
  [mod (module id (req ...) (expr ...))]
  [req (require id)]
  [expr var
        val
        (+ expr expr)
        (set! var expr)]
  [val number
       (quote id @ phase)]
  [var (id id)]
  [id variable-not-otherwise-mentioned])

(define-extended-language
  compiled/eval compiled
  [E hole
     (+ E expr)
     (+ val E)
     (set! var E)]
  [σ ([var val] ...)]
  [state (program / (id ...) / (id ...))]
  [st (σ / state)])

(define -->/ce
  (reduction-relation
   compiled/eval
   #:domain st
   [--> (σ / ((mod_0 ... (module id_0 ((require id_new) req ...) (expr ...)) mod_n ...) / (id_0 id_n ...) / (id_d ...)))
        (σ / ((mod_0 ... (module id_0 (req ...) (expr ...)) mod_n ...) / (id_new id_0 id_n ...) / (id_d ...)))
        "module require"]
   [--> (σ / (in-hole ((mod_0 ... (module id_0 () (E expr ...)) mod_n ...) / (id_0 id ...) / (id_d ...)) var))
        (σ / (in-hole ((mod_0 ... (module id_0 () (E expr ...)) mod_n ...) / (id_0 id ...) / (id_d ...)) val))
        "var ref"
        (where val (lookup σ var))]
   [--> (σ / (in-hole ((mod_0 ... (module id_0 () (E expr ...)) mod_n ...) / (id_0 id ...) / (id_d ...)) (+ number_0 number_1)))
        (σ / (in-hole ((mod_0 ... (module id_0 () (E expr ...)) mod_n ...) / (id_0 id ...) / (id_d ...)) ,(+ (term number_0) (term number_1))))
        "add"]
   [--> (σ_0 / (in-hole ((mod_0 ... (module id_0 () (E expr ...)) mod_n ...) / (id_0 id ...) / (id_d ...)) (set! var val)))
        (σ_1 / (in-hole ((mod_0 ... (module id_0 () (E expr ...)) mod_n ...) / (id_0 id ...) / (id_d ...)) val))
        "set!"
        (where σ_1 (assign σ_0 var val))]
   [--> (σ / ((mod_0 ... (module id_0 () (val expr ...)) mod_n ...) / (id_0 id_n ...) / (id_d ...)))
        (σ / ((mod_0 ... (module id_0 () (expr ...)) mod_n ...) / (id_0 id_n ...) / (id_d ...)))
        "expression done"]
   [--> (σ / ((mod_0 ... (module id_0 () ()) mod_n ...) / (id_0 id_n ...) / (id_d ...)))
        (σ / ((mod_0 ... mod_n ...) / (id_n ...) / (id_0 id_d ...)))
        "module done"]
   [--> (σ / ((mod ...) / (id_0 id_n ...) / (id_d0 ... id_0 id_dn ...)))
        (σ / ((mod ...) / (id_n ...) / (id_d0 ... id_0 id_dn ...)))
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
  #;(traces -->/ce (term (() / (,prog / (,main) / ()))))
  (match (apply-reduction-relation* -->/ce (term (() / (,prog / (,main) / ()))))
    [(list (list σ '/ (list prog* '/ (list) '/ done)))
     σ]
    [(and (list one two ...) ans)
     (error 'run "nondeterministic: ~a" ans)]
    [else
     (error 'run "leftover modules")]))

(define-extended-language
  expanded-core compiled
  [mod (module id (req ...) (def ...) (expr ...))]
  [req (require id @ phase)]
  [def (define id @ phase as expr)]
  [var id]
  [phase number])

(define-extended-language
  expanded expanded-core
  [var ....
       (id id)])

;; compile : expanded -> compiled
;; Many modules to many modules with resolved refs

;; demod : expanded id -> compiled
;; many modules to one module with resolve refs

(define-extended-language
  source expanded-core
  [var ....
       (ref id @ phase)])

#|
forall e:expanded, id:id,
 run(compile(e),id) = run(demod(e,id),id)
|#