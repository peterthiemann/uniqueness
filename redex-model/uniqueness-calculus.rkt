#lang racket

(require redex)
(require rackunit)

(define-language lam-rec
  ;; expressions
  (c ::=
     number boolean)
  (l ::=
     (variable-prefix l:))
  (p ::= +)
  (mode ::= in-place copy)
  (e ::=
     x (λ x T e) (app e e)
     c (p e e) (if e e e)
     (record (l e) ...)
     (get e l)
     (update mode e (l e) ...)
     )
  (x y ::=
     variable-not-otherwise-mentioned)
  ;; types
  (uvar ::= (variable-prefix u:))
  (u ::=
     READ WRITE uvar)
  (tvar ::= (variable-prefix t:))
  (T ::=
     tvar
     NUM BOOL
     (-> T T)
     (REC u (l T) ...))
  (S ::=
     (forall (uvar ...) (tvar ...) T))
  ;; typing environment
  (TEE ::= (x T))
  (TE ::=
      (TEE ...))
  ;; maybe type
  (MT ::= (left string) (right T))
  )

(define-extended-language lam-rec-runtime lam-rec
  (V ::=
     c
     A)
  (E ::=
     (app E e) (app V E)
     (p E e) (p V E)
     (if E e e)
     (record (l_0 V_0) ... (l E) (l_1 e_1) ...)
     (get E l)
     (update mode E (l e) ...) (update mode V (l_0 V_0) ... (l E) (l_1 e_1) ...)
     hole)
  (e ::=
     ....
     (sub e ϱ)
     )
  (A ::=
     (variable-prefix lam:)
     (variable-prefix rec:))
  (R ::=
     (record (l V) ...)
     (closure x T e ϱ))
  (ϱ ::=
     ((x V) ...))
  (Σ ::=
     ((A R) ...)))

(define-metafunction lam-rec-runtime
  remove-aux : y (x ...) (x ...) -> (x ...)
  [(remove-aux x (x x_0 ...) (y_0 ...))
   (x_0 ... y_0 ...)]
  [(remove-aux x (x_0 x_1 ...) (y_0 ...))
   (remove-aux x (x_1 ...) (x_0 y_0 ...))
   (side-condition (not (equal? (term x) (term x_0))))]
  [(remove-aux x () (y_0 ...))
   (y_0 ...)])

(define-metafunction lam-rec-runtime
  remove : y (x ...) -> (x ...)
  [(remove x (x_1 ...))
   (remove-aux x (x_1 ...) ())]
  )

(define-metafunction lam-rec-runtime
  remove-vars : (y ...) (x ...) -> (x ...)
  [(remove-vars () (x ...))
   (x ...)]
  [(remove-vars (y_0 y_1 ...) (x ...))
   (remove-vars y_0 (remove-vars (y_1 ...) (x ...)))])

(define-metafunction lam-rec-runtime
  union : (x ...) (x ...) ... -> (x ...)
  [(union (y_0 ...))
   (y_0 ...)]
  [(union (x_0 ...) (y_0 y_1 ...) (y_2 ...) ...)
   (union (x_0 ...) (y_1 ...) (y_2 ...) ...)
   (side-condition (member (term y_0) (term (x_0 ...))))]
  [(union (x_0 ...) (y_0 y_1 ...) (y_2 ...) ...)
   (union (y_0 x_0 ...) (y_1 ...) (y_2 ...) ...)
   (side-condition (not (member (term y_0) (term (x_0 ...)))))]
  [(union (x_0 ...) () (y_2 ...) ...)
   (union (x_0 ...) (y_2 ...) ...)]
  )

(define-metafunction lam-rec-runtime
  free : e -> (x ...)
  [(free c)
   ()]
  [(free x)
   (x)]
  [(free (λ x T e))
   (remove x (free e))]
  [(free (app e_0 e_1))
   (union (free e_0) (free e_1))]
  [(free (p e_0 e_1))
   (union (free e_0) (free e_1))]
  [(free (if e_0 e_1 e_2))
   (union (free e_0) (free e_1) (free e_2))]
  [(free (record (l_1 e_1) ...))
   (union (free e_1) ...)]
  [(free (get e l))
   (free e)]
  [(free (update mode e_0 (l_1 e_1) ...))
   (union (free e_0) (free e_1) ...)]
  [(free (sub e ϱ))
   (remove-vars (sub-vars ϱ) (free e))])

(define-metafunction lam-rec-runtime
  insert : Σ A R -> Σ
  [(insert ((A_1 R_1) ...) A_0 R_0)
   ((A_0 R_0) (A_1 R_1) ...)])

(define-metafunction lam-rec-runtime
  lookup : Σ A -> R
  [(lookup ((A_0 R_0) (A R) ...) A_0)
   R_0]
  [(lookup ((A_0 R_0) (A R) ...) A_1)
   (lookup ((A R) ...) A_1)
   (side-condition (not (equal? (term A_0) (term A_1))))])

(define-metafunction lam-rec-runtime
  insert-env : ϱ x V -> ϱ
  [(insert-env ((x_1 V_1) ...) x_0 V_0)
   ((x_0 V_0) (x_1 V_1) ...)])

(define-metafunction lam-rec-runtime
  lookup-env : ϱ x -> V
  [(lookup-env ((x_0 V_0) (x V) ...) x_0)
   V_0]
  [(lookup-env ((x_0 V_0) (x V) ...) x_1)
   (lookup-env ((x V) ...) x_1)
   (side-condition (not (equal? (term x_0) (term x_1))))])

(define-metafunction lam-rec-runtime
  lookup-rec : R l -> V
  [(lookup-rec (record (l_0 V_0) (l V) ...) l_0)
   V_0]
  [(lookup-rec (record (l_0 V_0) (l V) ...) l_1)
   (lookup-rec (record (l V) ...) l_1)
   (side-condition (not (equal? (term l_0) (term l_1))))])


(define-metafunction lam-rec-runtime
  sub-vars : ϱ -> (x ...)
  [(sub-vars ((x_1 V_1) ...))
   (x_1 ...)])

(define-metafunction lam-rec-runtime
  execute : p V V -> V
  [(execute + c_1 c_2)
   ,(+ (term c_1) (term c_2))]
  )

(define-metafunction lam-rec-runtime
  update-rec : R ((l V) ...) -> R
  [(update-rec (record (l_1 V_1) ...) ((l_2 V_2) ...))
   (record (l_2 V_2) ... (l_1 V_1) ...)
   (side-condition (disjoint (term (l_1 ...)) (term (l_2 ...))))]
  [(update-rec (record (l_1 V_1) ...) ((l_2 V_2) ...))
   (update-rec (record (l_2 V_2) ...) (remove-bindings (l_2 ...) ((l_1 V_1) ...) ()))
   (side-condition (not (disjoint (term (l_1 ...)) (term (l_2 ...)))))]
  )

(define-metafunction lam-rec-runtime
  remove-bindings : (l ...) ((l V) ...) ((l V) ...) -> ((l V) ...)
  [(remove-bindings (l ...) () any_0)
   any_0]
  [(remove-bindings (l_9 ...) ((l_0 V_0) (l_1 V_1) ...) ((l_2 V_2) ...))
   (remove-bindings (l_9 ...) ((l_1 V_1) ...) ((l_2 V_2) ...))
   (side-condition (member (term l_0) (term (l_9 ...))))]
  [(remove-bindings (l_9 ...) ((l_0 V_0) (l_1 V_1) ...) ((l_2 V_2) ...))
   (remove-bindings (l_9 ...) ((l_1 V_1) ...) ((l_0 V_0) (l_2 V_2) ...))
   (side-condition (not (member (term l_0) (term (l_9 ...)))))]
  )

(define (disjoint xs1 xs2)
  (let ((x1-in-xs2
         (for/fold ([x1-in-xs2 #f])
                   ([x1 xs1])
           (or (member x1 xs2) x1-in-xs2)))
        (x2-in-xs1
         (for/fold ([x2-in-xs1 #f])
                   ([x2 xs2])
           (or (member x2 xs1) x2-in-xs1))))
    (not (or x1-in-xs2 x2-in-xs1))))

(define-metafunction lam-rec-runtime
  keep-bindings : (x ...) ϱ -> ϱ
  [(keep-bindings (x_0 ...) ϱ_0)
   (keep-bindings-aux (x_0 ...) ϱ_0 ())]
  )
(define-metafunction lam-rec-runtime
  keep-bindings-aux : (x ...) ϱ ϱ -> ϱ
  [(keep-bindings-aux (x_0 ...) () ϱ_1)
   ϱ_1]
  [(keep-bindings-aux (x_0 ...) ((x_1 V_1) (x_2 V_2) ...) ((x_3 V_3) ...))
   (keep-bindings-aux (x_0 ...) ((x_2 V_2) ...) ((x_1 V_1) (x_3 V_3) ...))
   (side-condition (member (term x_1) (term (x_0 ...))))]
  [(keep-bindings-aux (x_0 ...) ((x_1 V_1) (x_2 V_2) ...) ((x_3 V_3) ...))
   (keep-bindings-aux (x_0 ...) ((x_2 V_2) ...) ((x_3 V_3) ...))
   (side-condition (not (member (term x_1) (term (x_0 ...)))))]
  )

(define lam-rec-red
  (reduction-relation
   lam-rec-runtime
   #:domain (Σ e)
   (--> (Σ (in-hole E (sub x ϱ)))
        (Σ (in-hole E (lookup-env ϱ x)))
        "var")
   
   (--> (Σ (in-hole E (sub (λ x T e_0) ϱ_0)))
        ((insert Σ lam:0 (closure x T e_0 ϱ_0)) (in-hole E lam:0))
        (fresh lam:0)
        (where ϱ_1 (keep-bindings (free (λ x T e_0)) ϱ_0))
        "lam-ϱ")

   (--> (Σ (in-hole E (λ x T e_0)))
        ((insert Σ lam:0 (closure x T e_0 ())) (in-hole E lam:0))
        (fresh lam:0)
        "lam")

   (--> (Σ (in-hole E (sub (app e_1 e_2) ϱ)))
        (Σ (in-hole E (app (sub e_1 ϱ) (sub e_2 ϱ))))
        "app-ϱ")

   (--> (Σ (in-hole E (app A_0 V_0)))
        (Σ (in-hole E (sub e (insert-env ϱ x V_0))))
        (where (closure x T e ϱ) (lookup Σ A_0))
        "βV")

   (--> (Σ (in-hole E (sub c ϱ)))
        (Σ (in-hole E c))
        "const-ϱ")

   (--> (Σ (in-hole E (sub (p e_1 e_2) ϱ)))
        (Σ (in-hole E (p (sub e_1 ϱ) (sub e_2 ϱ))))
        "prim-ϱ")

   (--> (Σ (in-hole E (p V_1 V_2)))
        (Σ (in-hole E (execute p V_1 V_2))))

   (--> (Σ (in-hole E (sub (if e_0 e_1 e_2) ϱ)))
        (Σ (in-hole E (if (sub e_0 ϱ) (sub e_1 ϱ) (sub e_2 ϱ))))
        "if-ϱ")

   (--> (Σ (in-hole E (if #t e_1 e_2)))
        (Σ (in-hole E e_1))
        "if-true")

   (--> (Σ (in-hole E (if #f e_1 e_2)))
        (Σ (in-hole E e_2)))

   (--> (Σ (in-hole E (sub (record (l_1 e_1) ...) ϱ)))
        (Σ (in-hole E (record (l_1 (sub e_1 ϱ)) ...)))
        "record-ϱ")

   (--> (Σ (in-hole E (record (l_1 V_1) ...)))
        ((insert Σ rec:0 (record (l_1 V_1) ...)) (in-hole E rec:0))
        (fresh rec:0)
        "record-alloc")

   (--> (Σ (in-hole E (sub (get e l) ϱ)))
        (Σ (in-hole E (get (sub e ϱ) l)))
        "get-ϱ")

   (--> (Σ (in-hole E (get A_0 l_0)))
        (Σ (in-hole E V_0))
        (where R_0 (lookup Σ A_0))
        (where V_0 (lookup-rec R_0 l_0))
        "get")

   (--> (Σ (in-hole E (sub (update mode e_0 (l_1 e_1) ...) ϱ)))
        (Σ (in-hole E (update mode (sub e_0 ϱ) (l_1 (sub e_1 ϱ)) ...)))
        "update-ϱ")

   (--> (Σ (in-hole E (update copy A_0 (l_1 V_1) ...)))
        ((insert Σ rec:0 (update-rec R_0 ((l_1 V_1) ...))) (in-hole E rec:0))
        (fresh rec:0)
        (where R_0 (lookup Σ A_0))
        "update-copy")

   (--> (Σ (in-hole E (update in-place A_0 (l_1 V_1) ...)))
        ((insert Σ A_0 (update-rec R_0 ((l_1 V_1) ...))) (in-hole E A_0))
        (where R_0 (lookup Σ A_0))
        "update-in-place")
   ))

;;; typing


(define-metafunction lam-rec-runtime
  lookup-tenv : TE x -> T
  [(lookup-tenv ((x_0 T_0) (x T) ...) x_0)
   T_0]
  [(lookup-tenv ((x_0 T_0) (x T) ...) x_1)
   (lookup-tenv ((x T) ...) x_1)
   (side-condition (not (equal? (term x_0) (term x_1))))])

(define-metafunction lam-rec-runtime
  lookup-trec : ((l T) ...) l -> MT
  [(lookup-trec ((l_0 T_0) (l T) ...) l_0)
   (right T_0)]
  [(lookup-trec ((l_0 T_0) (l T) ...) l_1)
   (lookup-trec ((l T) ...) l_1)
   (side-condition (not (equal? (term l_0) (term l_1))))]
  [(lookup-trec () l_0)
   (left "label not found")])

(define-metafunction lam-rec-runtime
  split-tenv* : TE (x ...) ..._1 -> (TE ..._1)
  [(split-tenv* TE)
   ()]
  [(split-tenv* TE (x ...))
   (TE)]
  [(split-tenv* TE (x_0 ...) (x_1 ...) ...)
   (TE_0 TE_2 ...)
   (where (TE_0 TE_1) (split-tenv TE (x_0 ...) (union (x_1 ...) ...)))
   (where (TE_2 ...) (split-tenv* TE_1 (x_1 ...) ...))
   ]
  )

;; split the environment
;; variables bound to splittable types get moved to both output environments
;; other variable get moved to the output environment where they occur
;; (if a variable of non-splittable type occurs in both subterms, we give up)
(define-metafunction lam-rec-runtime
  split-tenv : TE (x ...) (x ...) -> (TE TE)
  [(split-tenv TE_0 (x_1 ...) (y_1 ...))
   (split-tenv-aux TE_0 (x_1 ...) (y_1 ...) () ())])

(define-metafunction lam-rec-runtime
  split-tenv-aux : TE (x ...) (x ...) TE TE -> (TE TE)
  [(split-tenv-aux () (x_1 ...) (x_2 ...) TE_1 TE_2)
   (TE_1 TE_2)]

  [(split-tenv-aux ((x_0 T_0) (x_9 T_9) ...)
                   (x_1 ...) (x_2 ...)
                   (TEE_1 ...) (TEE_2 ...))
   (split-tenv-aux ((x_9 T_9) ...)
                   (x_1 ...) (x_2 ...)
                   ((x_0 T_0) TEE_1 ...) ((x_0 T_0) TEE_2 ...))
   (side-condition (term (splittable T_0)))
   ]

  [(split-tenv-aux ((x_0 T_0) (x_9 T_9) ...)
                   (x_1 ...) (x_2 ...)
                   (TEE_1 ...) (TEE_2 ...))
   (split-tenv-aux ((x_9 T_9) ...)
                   (x_1 ...) (x_2 ...)
                   ((x_0 T_0) TEE_1 ...) (TEE_2 ...))
   (side-condition (not (term (splittable T_0))))
   (side-condition (and (member (term x_0) (term (x_1 ...)))
                        (not (member (term x_0) (term (x_2 ...))))))
   ]

  [(split-tenv-aux ((x_0 T_0) (x_9 T_9) ...)
                   (x_1 ...) (x_2 ...)
                   (TEE_1 ...) (TEE_2 ...))
   (split-tenv-aux ((x_9 T_9) ...)
                   (x_1 ...) (x_2 ...)
                   (TEE_1 ...) ((x_0 T_0) TEE_2 ...))
   (side-condition (not (term (splittable T_0))))
   (side-condition (and (member (term x_0) (term (x_2 ...)))
                        (not (member (term x_0) (term (x_1 ...))))))
   ]

  ;; further cases require more knowledge about uses of (x_1 ...) and (x_2 ...)
  )

(define-relation lam-rec-runtime
  splittable ⊆ T
  [(splittable NUM)]
  [(splittable BOOL)]
  [(splittable (-> T_1 T_2))]
  [(splittable (REC READ (l_1 T_1) ...))
   (splittable T_1) ...])

(define (subset? xs1 xs2)
  (for/fold ([x1-in-xs2 #t])
            ([x1 xs1])
    (and (member x1 xs2) x1-in-xs2)))


(define (my-equal? x y)
  (display (list 'my-equal x y))
  (equal? x y))

(define (my-member x y)
  (let ((r (member x y)))
    (display (list 'my-member x y '= r))
    r))


(define-judgment-form lam-rec-runtime
  #:mode (typing I I I O)
  #:contract (typing TE e : T)

  [
   (typing TE_0 x : T_0)
   (where T_0 (lookup-tenv TE_0 x))
   "ty-var"
   ]


  [
   (typing TE_0 (app e_1 e_2) : T_0)
   (where (TE_1 TE_2) (split-tenv TE_0 (free e_1) (free e_2)))
   (typing TE_1 e_1 : (-> T_2 T_0))
   (typing TE_2 e_2 : T_2)
   "ty-app"
   ]

  [
   (typing (TEE_0 ...) (λ x_0 T_0 e_1) : (-> T_0 T_1))
   (typing ((x_0 T_0) TEE_0 ...) e_1 : T_1)
   "ty-lam"
   ]

  [
   (typing TE_0 number : NUM)
   "ty-num"
   ]

  [
   (typing TE_0 boolean : BOOL)
   "ty-bool"
   ]

  [
   (typing TE_0 (+ e_1 e_2) : NUM)
   (where (TE_1 TE_2) (split-tenv TE_0 (free e_1) (free e_2)))
   (typing TE_1 e_1 : NUM)
   (typing TE_2 e_2 : NUM)
   "ty-add"
   ]

  [
   (typing TE_0 (record (l_1 e_1) ...) : (REC READ (l_1 T_1) ...))
   (where (TE_1 ...) (split-tenv* TE_0 (free e_1) ...))
   (typing TE_1 e_1 : T_1) ...
   "ty-record"
   ]

  [
   (typing TE_0 (get e_0 l_0) : T_0)
   (typing TE_0 e_0 : (REC u (l_1 T_1) ...))
   (where (right T_0) (lookup-trec ((l_1 T_1) ...) l_0))
   "ty-get"
   ]

  [
   (typing TE_0 (update mode e_9 (l_1 e_1) ...) : (REC READ (l_2 T_2) ...))
   (where (TE_9 TE_1 ...) (split-tenv* TE_0 (free e_9) (free e_1) ...))
   (typing TE_9 e_9 : (REC READ (l_2 T_2) ...))
   (where ((right T_3) ...) ((lookup-trec ((l_2 T_2) ...) l_1) ...))
   (typing TE_1 e_1 : T_3) ...
   "ty-update"
   ]
  
  )
;; examples

;(define (test-typing te ty)
;  (judgment-holds (typing () ,te : ,ty)))

(define ex1 (term (app (λ x BOOL x) #t)))
(check-true (judgment-holds (typing () ,ex1 : BOOL)))

(define ex2 (term (record (l:a 1))))
(check-true (judgment-holds (typing () ,ex2 : (REC u (l:a NUM)))))

(define ex4 (term (record)))
(check-true (judgment-holds (typing () ,ex4 : (REC u))))

(define ex3 (term (get (record (l:a 1)) l:a)))
(check-true (judgment-holds (typing () ,ex3 : NUM)))

(define ex5 (term (get (record (l:a 1)) l:b)))
(check-false (judgment-holds (typing () ,ex5 : T)))

(define ex6 (term (update in-place (record (l:a 1)) (l:a #f))))
(check-false (judgment-holds (typing () ,ex6 : T)))

(define ex7 (term (update in-place (record (l:a 1)) (l:a 42))))
(check-true (judgment-holds (typing () ,ex7 : T)))

(check-true
 (judgment-holds
  (typing () (update in-place (record (l:a 1) (l:b #f)) (l:b #t) (l:a 42) ) : T)))
(check-false
 (judgment-holds
  (typing () (update in-place (record (l:a 1) (l:b #f)) (l:b #t) (l:a 42) (l:c #f) ) : T)))

