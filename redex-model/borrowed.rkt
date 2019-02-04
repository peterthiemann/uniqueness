#lang racket

(require redex)

(define-language lam-borrow
  ;; expressions
  (c ::=
     unit number boolean
     init observe update close
     )
  (p ::= + - * / = < > <= >=)
  (m ::= aff unr)
  (I ::= imm mut)
  (e ::=
     x (λ m (x ...) T e) (λ& I m (x ...) T e) (app e e ...)
     (let x e e) (let& I x e e)
     c (p e e) (if e e e)
     (record m e ...)
     (elim-record (x ...) e e)
     )
  (x y ::=
     variable-not-otherwise-mentioned)
  )

(define-extended-language lam-borrow-runtime lam-borrow
  (V ::=
     c
     A
     (& I A)
     init observe update close)
  (E ::=
     (app E e ...) (app V V ... E e ...)
     (let x E e) (let& I x E e)
     (p E e) (p V E)
     (if E e e)
     (record m V ... E e ...)
     (elim-record (x ...) E e)
     hole)
  (e ::=
     ....
     (& I A))
  (A ::=
     (variable-prefix res:)
     (variable-prefix loc:)
     (variable-prefix cls:))
  (R ::=
     (record m V ...)
     (closure m xs T e)
     (closure& I m xs T e)
     initialized closed)
  (ϱ ::=
     ((x V) ...))
  (Σ ::=
     ((A R) ...))
  (xs ::= (x ...))
  (Vs ::= (V ...))
  )

(define-metafunction lam-borrow-runtime
  drop-vars : xs ϱ -> ϱ
  [(drop-vars () ϱ)
   ϱ]
  [(drop-vars (x_0 x_1 ...) ϱ_0)
   (drop-vars (x_1 ...) (drop-var x_0 ϱ_0 ()))])

(define-metafunction lam-borrow-runtime
  drop-var : x ϱ ϱ -> ϱ
  [(drop-var x_0 () ϱ_0)
   ϱ_0]
  [(drop-var y_0 ((x_0 V_0) (x_1 V_1) ...) ((x_9 V_9) ...))
   ((x_9 V_9) ... (x_1 V_1) ...)
   (side-condition (equal? (term x_0) (term y_0)))]
  [(drop-var y_0 ((x_0 V_0) (x_1 V_1) ...) ((x_9 V_9) ...))
   (drop-var y_0 ((x_1 V_1) ...) ((x_0 V_0) (x_9 V_9) ...))
   (side-condition (not (equal? (term x_0) (term y_0))))])

(define-metafunction lam-borrow-runtime
  subst : ϱ e -> e
  [(subst ((x_0 V_0) (x_1 V_1) ...) y_0)
   V_0
   (side-condition (equal? (term x_0) (term y_0)))]
  [(subst ((x_0 V_0) (x_1 V_1) ...) y_0)
   (subst ((x_1 V_1) ...) y_0)
   (side-condition (not (equal? (term x_0) (term y_0))))]
  [(subst () y_0)
   y_0]
  [(subst ϱ_0 (λ m_0 xs_0 T e_0))
   (λ m_0 xs_0 T (subst (drop-vars xs_0 ϱ_0) e_0))]
  [(subst ϱ_0 (app e_0 e_1 ...))
   (app (subst ϱ_0 e_0) (subst ϱ_0 e_1) ...)]
  [(subst ϱ_0 (let x_0 e_1 e_2))
   (let x_0 (subst ϱ_0 e_1) (subst (drop-var x_0 ϱ_0 ()) e_2))]
  [(subst ϱ_0 c_0)
   c_0]
  [(subst ϱ_0 (p_0 e_1 e_2))
   (p_0 (subst ϱ_0 e_1) (subst ϱ_0 e_2))]
  [(subst ϱ_0 (if e_0 e_1 e_2))
   (if (subst ϱ_0 e_0) (subst ϱ_0 e_1) (subst ϱ_0 e_2))]
  [(subst ϱ_0 (record m_0 e_0 ...))
   (record m_0 (subst ϱ_0 e_0) ...)]
  [(subst ϱ_0 (elim-record xs_0 e_1 e_2))
   (elim-record xs_0 (subst ϱ_0 e_1) (subst (drop-vars xs_0 ϱ_0) e_2))]
  )

(define-metafunction lam-borrow-runtime
  insert : Σ A R -> Σ
  [(insert ((A_1 R_1) ...) A_0 R_0)
   ((A_0 R_0) (A_1 R_1) ...)])

(define-metafunction lam-borrow-runtime
  remove : Σ A -> Σ
  [(remove ((A_0 R_0) ... (A_1 R_1) (A_2 R_2) ...) A_9)
   ((A_0 R_0) ... (A_2 R_2) ...)
   (side-condition (equal? (term A_1) (term A_9)))])

(define-metafunction lam-borrow-runtime
  remove-if-aff : m Σ A -> Σ
  [(remove-if-aff aff Σ_0 A_0)
   (remove Σ_0 A_0)]
  [(remove-if-aff unr Σ_0 A_0)
   Σ_0])

(define-metafunction lam-borrow-runtime
  lookup : Σ A -> R
  [(lookup ((A_0 R_0) (A R) ...) A_0)
   R_0]
  [(lookup ((A_0 R_0) (A R) ...) A_1)
   (lookup ((A R) ...) A_1)
   (side-condition (not (equal? (term A_0) (term A_1))))])

(define-metafunction lam-borrow-runtime
  zip-helper : xs Vs ϱ -> ϱ
  [(zip-helper () () ϱ_0)
   ϱ_0]
  [(zip-helper (x_0 x_1 ...) (V_0 V_1 ...) ((x_9 V_9) ...))
   (zip-helper (x_1 ...) (V_1 ...) ((x_0 V_0) (x_9 V_9) ...))])

(define-metafunction lam-borrow-runtime
  zip : xs Vs -> ϱ
  [(zip xs_0 Vs_0)
   (zip-helper xs_0 Vs_0 ())])

(define-metafunction lam-borrow-runtime
  I-restrict : I I -> I
  [(I-restrict imm imm)
   imm]
  [(I-restrict mut mut)
   mut]
  [(I-restrict imm mut)
   imm])

(define-metafunction lam-borrow-runtime
  amp : I V -> V
  [(amp I_0 (& I_1 A_0))
   (& (I-restrict I_0 I_1) A_0)]
  [(amp I_0 A_0)
   (& I_0 A_0)]
  [(amp I_0 c)
   c])

;     x (λ m (x ...) T e) (app e e ...) (let x e e)
;     c (p e e) (if e e e)
;     (record m e ...)
;     (elim-record (x ...) e e)

(define lam-borrow-red
  (reduction-relation
   lam-borrow-runtime
   #:domain (Σ e)
   ;; lambda calculus
   (-->
    (Σ (in-hole E (λ m_0 xs_0 T e_0)))
    ((insert Σ cls:0 (closure m_0 xs_0 T e_0)) (in-hole E cls:0))
    (fresh cls:0))
;   (-->
;    (Σ (in-hole E (app A_0 V_1 ...)))
;    (Σ (in-hole E (subst (zip xs_0 (V_1 ...)) e_0)))
;    (where (closure unr xs_0 T e_0) (lookup Σ A_0)))
   (-->
    (Σ_0 (in-hole E (app A_0 V_1 ...)))
    ((remove-if-aff m_0 Σ_0 A_0) (in-hole E (subst (zip xs_0 (V_1 ...)) e_0)))
    (where (closure m_0 xs_0 T e_0) (lookup Σ_0 A_0)))
   (-->
    (Σ (in-hole E (p_0 V_1 V_2)))
    (Σ (in-hole E ,(apply (eval (term p_0)) (term (V_1 V_2))))))
   (-->
    (Σ (in-hole E (let x_0 V_0 e_2)))
    (Σ (in-hole E (subst ((x_0 V_0)) e_2))))
   (-->
    (Σ (in-hole E (if #t e_1 e_2)))
    (Σ (in-hole E e_1)))
   (-->
    (Σ (in-hole E (if #f e_1 e_2)))
    (Σ (in-hole E e_2)))
   ;; borrowing
   (-->
    (Σ (in-hole E (let& I_0 x_0 V_0 e_0)))
    (Σ (in-hole E (subst ((x_0 (amp I_0 V_0))) e_0))))
   (-->
    (Σ (in-hole E (elim-record xs_0 (& I_0 A_0) e_0)))
    (Σ (in-hole E (subst ϱ_0 e_0)))
    (where (record m_0 V_0 ...) (lookup Σ A_0))
    (where ϱ_0 (zip xs_0 ((amp I_0 V_0) ...)))
    )
   (-->
    (Σ (in-hole E (app observe (& I_0 A_0))))
    (Σ (in-hole E (app observe A_0))))
   (-->
    (Σ (in-hole E (app update (& mut A_0) V_0)))
    (Σ (in-hole E (app update A_0 V_0))))
   (-->
    (Σ (in-hole E (λ& I_0 m_0 xs_0 T e_0)))
    ((insert Σ cls:0 (closure& I_0 m_0 xs_0 T e_0)) (in-hole E cls:0))
    (fresh cls:0))
   (-->
    (Σ (in-hole E (app A_0 V_1 ...)))
    (Σ (in-hole E (subst (zip xs_0 ((amp imm V_1) ...)) e_0)))
    (where (closure& I_0 unr xs_0 T e_0) (lookup Σ A_0)))
   (-->
    (Σ (in-hole E (app A_0 V_1 ...)))
    ((remove Σ A_0) (in-hole E (subst (zip xs_0 ((amp imm V_1) ...)) e_0)))
    (where (closure& I_0 aff xs_0 T e_0) (lookup Σ A_0)))
   ;; memory reductions
   (-->
    (Σ (in-hole E (record m_0 V_0 ...)))
    ((insert Σ loc:0 (record m_0 V_0 ...)) (in-hole E loc:0))
    (fresh loc:0)
    )
   (-->
    (Σ (in-hole E (elim-record xs_0 A_0 e_0)))
    (Σ (in-hole E (subst ϱ_0 e_0)))
    (where (record unr V_0 ...) (lookup Σ A_0))
    (where ϱ_0 (zip xs_0 (V_0 ...)))
    )
   (-->
    (Σ (in-hole E (elim-record xs_0 A_0 e_0)))
    ((remove Σ A_0) (in-hole E (subst ϱ_0 e_0)))
    (where (record aff V_0 ...) (lookup Σ A_0))
    (where ϱ_0 (zip xs_0 (V_0 ...)))
    )
   ;; resource reductions
   (-->
    (Σ (in-hole E (app init V_0)))
    ((insert Σ res:0 initialized) (in-hole E res:0))
    (fresh res:0))
   (-->
    (Σ (in-hole E (app close A_0)))
    ((insert (remove Σ A_0) A_0 closed) (in-hole E unit))
    (where R_0 (lookup Σ A_0))
    (side-condition (equal? (term R_0) (term initialized))))
   (-->
    (Σ (in-hole E (app observe A_0)))
    (Σ (in-hole E 42))
    (where R_0 (lookup Σ A_0))
    (side-condition (equal? (term R_0) (term initialized))))
   (-->
    (Σ (in-hole E (app update A_0 V_0)))
    (Σ (in-hole E unit))
    (where R_0 (lookup Σ A_0))
    (side-condition (equal? (term R_0) (term initialized))))
   ))
