------------------------------------------------------------------------
-- Presentations of groups
--
-- Symmetric generators.  H_[b,a] for b > a is X_[a,b] H_[a,b] X_[a,b]
-- (relation (e2) of Appendix A), and X_[b,a] is X_[a,b] (e1): Hs a b
-- and Xs a b are these words for any distinct a, b (and ε for a = b).
-- Hs a b acts on the entries a, b as (v_a + v_b)/√2, (v_a - v_b)/√2,
-- whatever the order of a and b.
--
-- Conjugation by X_[p,q] relabels them along the transposition
-- τ = (p q) (relabel-Hs, relabel-Xs, relabel-Z): this lets a relation
-- among symmetric words that holds for one ordering of its indices be
-- moved to any other (the paper's "for any order of the subscripts").
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ)

module Examples.Groups.Real-Clifford+CH-TwoLevel.Symmetric {n : ℕ} where

open import Data.Bool.Base using (if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
import Data.List.Base as List
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Product.Base using (_,_)
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_ ; ≢-sym)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; recompute ; dec-true ; dec-false)
import Relation.Binary.Reasoning.Setoid as SR

open import Notations using (auto)
open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n}

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  variable
    a b c p q : Fin n

  -- A relevant order proof from an irrelevant one.
  rc : .(a < b) → a < b
  rc {a = a} {b} lt = recompute (a FinP.<? b) lt

  <⇒≢′ : .(a < b) → a ≢ b
  <⇒≢′ lt e = FinP.<-irrefl e (rc lt)

  >⇒≢′ : .(a < b) → b ≢ a
  >⇒≢′ lt e = <⇒≢′ lt (≡.sym e)

------------------------------------------------------------------------
-- The symmetric words

HsT : (a b : Fin n) → Tri (a < b) (a ≡ b) (b < a) → Word (Gen n)
HsT a b (tri< lt _ _) = H a b lt
HsT a b (tri≈ _ _ _)  = ε
HsT a b (tri> _ _ gt) = X b a gt • H b a gt • X b a gt

Hs : Fin n → Fin n → Word (Gen n)
Hs a b = HsT a b (FinP.<-cmp a b)

XsT : (a b : Fin n) → Tri (a < b) (a ≡ b) (b < a) → Word (Gen n)
XsT a b (tri< lt _ _) = X a b lt
XsT a b (tri≈ _ _ _)  = ε
XsT a b (tri> _ _ gt) = X b a gt

Xs : Fin n → Fin n → Word (Gen n)
Xs a b = XsT a b (FinP.<-cmp a b)

Hs-< : .(lt : a < b) → Hs a b ≡ H a b lt
Hs-< {a = a} {b} lt with FinP.<-cmp a b
... | tri< _ _ _ = ≡.refl
... | tri≈ ¬lt _ _ = ⊥-elim (¬lt (rc lt))
... | tri> ¬lt _ _ = ⊥-elim (¬lt (rc lt))

Hs-> : .(gt : b < a) → Hs a b ≡ X b a gt • H b a gt • X b a gt
Hs-> {b = b} {a} gt with FinP.<-cmp a b
... | tri< _ _ ¬gt = ⊥-elim (¬gt (rc gt))
... | tri≈ _ _ ¬gt = ⊥-elim (¬gt (rc gt))
... | tri> _ _ _ = ≡.refl

Xs-< : .(lt : a < b) → Xs a b ≡ X a b lt
Xs-< {a = a} {b} lt with FinP.<-cmp a b
... | tri< _ _ _ = ≡.refl
... | tri≈ ¬lt _ _ = ⊥-elim (¬lt (rc lt))
... | tri> ¬lt _ _ = ⊥-elim (¬lt (rc lt))

Xs-> : .(gt : b < a) → Xs a b ≡ X b a gt
Xs-> {b = b} {a} gt with FinP.<-cmp a b
... | tri< _ _ ¬gt = ⊥-elim (¬gt (rc gt))
... | tri≈ _ _ ¬gt = ⊥-elim (¬gt (rc gt))
... | tri> _ _ _ = ≡.refl

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

  -- Case analysis on the order of two distinct indices.
  by-order : ∀ {A : Set} → a ≢ b → (.(a < b) → A) → (.(b < a) → A) → A
  by-order {a = a} {b} a≢b f g with FinP.<-cmp a b
  ... | tri< lt _ _ = f lt
  ... | tri≈ _ e _ = ⊥-elim (a≢b e)
  ... | tri> _ _ gt = g gt

-- Xs is symmetric.
Xs-sym : a ≢ b → Xs a b ≈ Xs b a
Xs-sym {a = a} {b} a≢b = by-order a≢b
  (λ lt → trans (refl′ (Xs-< lt)) (refl′ (≡.sym (Xs-> lt))))
  (λ gt → trans (refl′ (Xs-> gt)) (refl′ (≡.sym (Xs-< gt))))

Xs-Xs : a ≢ b → Xs a b • Xs a b ≈ ε
Xs-Xs {a = a} {b} a≢b = by-order a≢b
  (λ lt → trans (cong (refl′ (Xs-< lt)) (refl′ (Xs-< lt))) (X-X lt))
  (λ gt → trans (cong (refl′ (Xs-> gt)) (refl′ (Xs-> gt))) (X-X gt))

-- X H X X H X X ≈ ε.
private
  XHX-XHX : .(lt : a < b) → (X a b lt • H a b lt • X a b lt) • (X a b lt • H a b lt • X a b lt) ≈ ε
  XHX-XHX {a = a} {b} lt = begin
    (X′ • H′ • X′) • (X′ • H′ • X′)       ≈⟨ by-assoc auto ⟩
    X′ • H′ • (X′ • X′) • H′ • X′         ≈⟨ cright cright cleft X-X lt ⟩
    X′ • H′ • ε • H′ • X′                 ≈⟨ cright cright left-unit ⟩
    X′ • H′ • H′ • X′                     ≈⟨ cright sym assoc ⟩
    X′ • (H′ • H′) • X′                   ≈⟨ cright cleft H-H lt ⟩
    X′ • ε • X′                           ≈⟨ cright left-unit ⟩
    X′ • X′                               ≈⟨ X-X lt ⟩
    ε                                     ∎
    where
    X′ = X a b lt
    H′ = H a b lt

Hs-Hs : a ≢ b → Hs a b • Hs a b ≈ ε
Hs-Hs {a = a} {b} a≢b = by-order a≢b
  (λ lt → trans (cong (refl′ (Hs-< lt)) (refl′ (Hs-< lt))) (H-H lt))
  (λ gt → trans (cong (refl′ (Hs-> gt)) (refl′ (Hs-> gt))) (XHX-XHX gt))

private
  flip-gt : .(gt : b < a) → Xs a b • Hs a b • Xs a b ≈ Hs b a
  flip-gt {b = b} {a} gt = begin
    Xs a b • Hs a b • Xs a b
      ≈⟨ cong (refl′ (Xs-> gt)) (cong (refl′ (Hs-> gt)) (refl′ (Xs-> gt))) ⟩
    X′ • (X′ • H′ • X′) • X′            ≈⟨ by-assoc auto ⟩
    (X′ • X′) • H′ • (X′ • X′)          ≈⟨ cong (X-X gt) (cright X-X gt) ⟩
    ε • H′ • ε                          ≈⟨ trans left-unit right-unit ⟩
    H′                                  ≈⟨ refl′ (≡.sym (Hs-< gt)) ⟩
    Hs b a                              ∎
    where
    X′ = X b a gt
    H′ = H b a gt

-- Hs b a = Xs a b Hs a b Xs a b.
Hs-flip : a ≢ b → Hs b a ≈ Xs a b • Hs a b • Xs a b
Hs-flip {a = a} {b} a≢b = by-order a≢b
  (λ lt → trans (refl′ (Hs-> lt))
                (sym (cong (refl′ (Xs-< lt)) (cong (refl′ (Hs-< lt)) (refl′ (Xs-< lt))))))
  (λ gt → sym (flip-gt gt))

-- Hs on two pairs apart from each other commute.
Hs-comm : p ≢ q → a ≢ b → p ≢ a → p ≢ b → q ≢ a → q ≢ b → Hs p q • Hs a b ≈ Hs a b • Hs p q
Hs-comm {p = p} {q} {a} {b} pq ab pa pb qa qb = comm-words (Hs p q) (Hs a b) (ap (FinP.<-cmp p q) (FinP.<-cmp a b))
  where
  pr : ∀ {x y z w : Fin n} → x ≢ z → x ≢ w → y ≢ z → y ≢ w →
       All (λ t → All (t ≢_) (z List.∷ w List.∷ List.[])) (x List.∷ y List.∷ List.[])
  pr xz xw yz yw = (xz ∷ xw ∷ []) ∷ (yz ∷ yw ∷ []) ∷ []
  ap : (t : Tri (p < q) (p ≡ q) (q < p)) (u : Tri (a < b) (a ≡ b) (b < a)) → Apartʷʷ (HsT p q t) (HsT a b u)
  ap (tri≈ _ e _) _ = ⊥-elim (pq e)
  ap _ (tri≈ _ e _) = ⊥-elim (ab e)
  ap (tri< _ _ _) (tri< _ _ _) = pr pa pb qa qb
  ap (tri< _ _ _) (tri> _ _ _) = pr pb pa qb qa , pr pb pa qb qa , pr pb pa qb qa
  ap (tri> _ _ _) (tri< _ _ _) = pr qa qb pa pb , pr qa qb pa pb , pr qa qb pa pb
  ap (tri> _ _ _) (tri> _ _ _) = (pr qb qa pb pa , pr qb qa pb pa , pr qb qa pb pa) ,
                                 (pr qb qa pb pa , pr qb qa pb pa , pr qb qa pb pa) ,
                                 (pr qb qa pb pa , pr qb qa pb pa , pr qb qa pb pa)

------------------------------------------------------------------------
-- The transposition (p q)

τ : Fin n → Fin n → Fin n → Fin n
τ p q x = if does (x FinP.≟ p) then q else (if does (x FinP.≟ q) then p else x)

τ-p : ∀ (p q : Fin n) → τ p q p ≡ q
τ-p p q = ≡.cong (λ d → if d then q else (if does (p FinP.≟ q) then p else p)) (dec-true (p FinP.≟ p) ≡.refl)

τ-q : ∀ (p q : Fin n) → p ≢ q → τ p q q ≡ p
τ-q p q p≢q =
  ≡.trans (≡.cong (λ d → if d then q else (if does (q FinP.≟ q) then p else q)) (dec-false (q FinP.≟ p) (p≢q ∘ ≡.sym)))
          (≡.cong (λ d → if d then p else q) (dec-true (q FinP.≟ q) ≡.refl))

τ-o : ∀ (p q a : Fin n) → a ≢ p → a ≢ q → τ p q a ≡ a
τ-o p q a a≢p a≢q =
  ≡.trans (≡.cong (λ d → if d then q else (if does (a FinP.≟ q) then p else a)) (dec-false (a FinP.≟ p) a≢p))
          (≡.cong (λ d → if d then p else a) (dec-false (a FinP.≟ q) a≢q))

------------------------------------------------------------------------
-- Conjugation by X_[p,q]

private
  -- X (X B X) X = B.
  XXBXX : .(pq : p < q) → ∀ B → X p q pq • (X p q pq • B • X p q pq) • X p q pq ≈ B
  XXBXX pq B = begin
    X′ • (X′ • B • X′) • X′           ≈⟨ cright assoc ⟩
    X′ • X′ • (B • X′) • X′           ≈⟨ cright cright assoc ⟩
    X′ • X′ • B • (X′ • X′)           ≈⟨ cright cright cright X-X pq ⟩
    X′ • X′ • B • ε                   ≈⟨ cright cright right-unit ⟩
    X′ • X′ • B                       ≈⟨ sym assoc ⟩
    (X′ • X′) • B                     ≈⟨ cleft X-X pq ⟩
    ε • B                             ≈⟨ left-unit ⟩
    B                                 ∎
    where X′ = X _ _ pq

  -- From A X = X B: X A X = B.
  from-conj : ∀ {A B} .(pq : p < q) → A • X p q pq ≈ X p q pq • B → X p q pq • A • X p q pq ≈ B
  from-conj pq h = sym (conj-X pq h)

  -- From A X = X B: X B X = A.
  from-conj′ : ∀ {A B} .(pq : p < q) → A • X p q pq ≈ X p q pq • B → X p q pq • B • X p q pq ≈ A
  from-conj′ pq h = sym (conj-X′ pq h)

  apart-XH : ∀ .(pq : p < q) .(ab : a < b) → a ≢ p → a ≢ q → b ≢ p → b ≢ q →
             Apart (X-gen p q pq) (H-gen a b ab)
  apart-XH pq ab ap aq bp bq = ((ap ∘ ≡.sym) ∷ (bp ∘ ≡.sym) ∷ []) ∷ ((aq ∘ ≡.sym) ∷ (bq ∘ ≡.sym) ∷ []) ∷ []

  -- A generator apart from X_[p,q] is fixed by conjugation.
  conj-apart : ∀ (g : Gen n) .(pq : p < q) → Apart (X-gen p q pq) g → X p q pq • [ g ]ʷ • X p q pq ≈ [ g ]ʷ
  conj-apart g pq ap = begin
    X′ • [ g ]ʷ • X′           ≈⟨ cright sym (comm-gen (X-gen _ _ pq) g ap) ⟩
    X′ • X′ • [ g ]ʷ           ≈⟨ sym assoc ⟩
    (X′ • X′) • [ g ]ʷ         ≈⟨ cleft X-X pq ⟩
    ε • [ g ]ʷ                 ≈⟨ left-unit ⟩
    [ g ]ʷ                     ∎
    where X′ = X _ _ pq

-- Z: X_[p,q] Z_[a] X_[p,q] = Z_[τ a].
private
  relabel-Z′ : ∀ {p q a} (pq : p < q) → Dec (a ≡ p) → Dec (a ≡ q) → X p q pq • Z a • X p q pq ≈ Z (τ p q a)
  relabel-Z′ {p} {q} pq (yes ≡.refl) _ = trans (from-conj pq (axiom (c1 pq))) (refl′ (≡.cong Z (≡.sym (τ-p p q))))
  relabel-Z′ {p} {q} pq (no a≢p) (yes ≡.refl) = trans (from-conj′ pq (axiom (c1 pq))) (refl′ (≡.cong Z (≡.sym (τ-q p q (<⇒≢′ pq)))))
  relabel-Z′ {p} {q} {a} pq (no a≢p) (no a≢q) =
    trans (conj-apart (Z-gen a) pq (((a≢p ∘ ≡.sym) ∷ []) ∷ ((a≢q ∘ ≡.sym) ∷ []) ∷ []))
          (refl′ (≡.cong Z (≡.sym (τ-o p q a a≢p a≢q))))

relabel-Z : ∀ (pq : p < q) a → X p q pq • Z a • X p q pq ≈ Z (τ p q a)
relabel-Z {p = p} {q} pq a = relabel-Z′ pq (a FinP.≟ p) (a FinP.≟ q)

-- H, in increasing order: X_[p,q] H_[a,b] X_[p,q] = Hs (τ a) (τ b).
private
  relabel-H′ : ∀ {p q a b} (pq : p < q) (ab : a < b) → Dec (a ≡ p) → Dec (a ≡ q) → Dec (b ≡ p) → Dec (b ≡ q) →
               X p q pq • H a b ab • X p q pq ≈ Hs (τ p q a) (τ p q b)
  -- a = p, b = q: Hs q p by definition.
  relabel-H′ {p} {q} {a} {b} pq ab (yes ≡.refl) _ _ (yes ≡.refl) =
    trans (refl′ (≡.sym (Hs-> pq))) (refl′ (≡.cong₂ Hs (≡.sym (τ-p p q)) (≡.sym (τ-q p q (<⇒≢′ pq)))))
  -- a = p, b ≠ q.
  relabel-H′ {p} {q} {a} {b} pq ab (yes ≡.refl) _ _ (no b≢q) with FinP.<-cmp q b
  ... | tri< q<b _ _ =
    -- (c4) at p < q < b.
    trans (from-conj′ pq (axiom (c4 pq q<b)))
          (trans (refl′ (≡.sym (Hs-< q<b))) (refl′ (≡.cong₂ Hs (≡.sym (τ-p p q)) (≡.sym (τ-o p q b (>⇒≢′ ab) b≢q)))))
  ... | tri≈ _ q≡b _ = ⊥-elim (b≢q (≡.sym q≡b))
  ... | tri> _ _ b<q =
    -- p < b < q: X_pq H_pb X_pq = X_bq H_bq X_bq = Hs q b.
    trans core (trans (refl′ (≡.sym (Hs-> b<q))) (refl′ (≡.cong₂ Hs (≡.sym (τ-p p q)) (≡.sym (τ-o p q b (>⇒≢′ ab) b≢q)))))
    where
    ab′ = rc ab
    Xpq = X p q pq
    Xbq = X b q b<q
    Xpb = X p b ab
    Hbq = H b q b<q
    -- (c5): H_pb = X_bq H_pq X_bq; (c4): H_pq = X_pb H_bq X_pb.
    h1 : H p b ab ≈ Xbq • H p q pq • Xbq
    h1 = conj-X b<q (axiom (c5 ab′ b<q))
    h2 : H p q pq ≈ Xpb • Hbq • Xpb
    h2 = conj-X ab (axiom (c4 ab′ b<q))
    -- (c3): X_pq X_bq = X_bq X_pb, and its inverse X_pb X_bq = X_bq X_pq.
    x3 : Xpq • Xbq ≈ Xbq • Xpb
    x3 = axiom (c3 ab′ b<q)
    x3′ : Xpb • Xbq ≈ Xbq • Xpq
    x3′ = begin
      Xpb • Xbq                                   ≈⟨ sym left-unit ⟩
      ε • Xpb • Xbq                               ≈⟨ cleft sym (X-X b<q) ⟩
      (Xbq • Xbq) • Xpb • Xbq                     ≈⟨ by-assoc auto ⟩
      Xbq • (Xbq • Xpb) • Xbq                     ≈⟨ cright cleft sym x3 ⟩
      Xbq • (Xpq • Xbq) • Xbq                     ≈⟨ by-assoc auto ⟩
      Xbq • Xpq • (Xbq • Xbq)                     ≈⟨ cright cright X-X b<q ⟩
      Xbq • Xpq • ε                               ≈⟨ cright right-unit ⟩
      Xbq • Xpq                                   ∎
    core : Xpq • H p b ab • Xpq ≈ Xbq • Hbq • Xbq
    core = begin
      Xpq • H p b ab • Xpq                        ≈⟨ cright cleft h1 ⟩
      Xpq • (Xbq • H p q pq • Xbq) • Xpq          ≈⟨ cright cleft cright cleft h2 ⟩
      Xpq • (Xbq • (Xpb • Hbq • Xpb) • Xbq) • Xpq ≈⟨ by-assoc auto ⟩
      Xpq • (Xbq • Xpb) • Hbq • (Xpb • Xbq) • Xpq ≈⟨ cright cong (sym x3) (cright cleft x3′) ⟩
      Xpq • (Xpq • Xbq) • Hbq • (Xbq • Xpq) • Xpq ≈⟨ by-assoc auto ⟩
      (Xpq • Xpq) • Xbq • Hbq • Xbq • (Xpq • Xpq) ≈⟨ cong (X-X pq) (cright cright cright X-X pq) ⟩
      ε • Xbq • Hbq • Xbq • ε                     ≈⟨ trans left-unit (by-assoc auto) ⟩
      Xbq • Hbq • Xbq                             ∎
  -- a = q (so q < b): (c4) at p < q < b.
  relabel-H′ {p} {q} {a} {b} pq ab (no a≢p) (yes ≡.refl) _ _ =
    trans (from-conj pq (axiom (c4 (rc pq) (rc ab))))
          (trans (refl′ (≡.sym (Hs-< (FinP.<-trans (rc pq) (rc ab)))))
                 (refl′ (≡.cong₂ Hs (≡.sym (τ-q p q (<⇒≢′ pq))) (≡.sym (τ-o p q b (>⇒≢′ (FinP.<-trans (rc pq) (rc ab))) (>⇒≢′ ab))))))
  -- b = p (so a < p): (c5) at a < p < q.
  relabel-H′ {p} {q} {a} {b} pq ab (no a≢p) (no a≢q) (yes ≡.refl) _ =
    trans (from-conj′ pq (axiom (c5 (rc ab) (rc pq))))
          (trans (refl′ (≡.sym (Hs-< (FinP.<-trans (rc ab) (rc pq)))))
                 (refl′ (≡.cong₂ Hs (≡.sym (τ-o p q a a≢p a≢q)) (≡.sym (τ-p p q)))))
  -- b = q, a ≠ p.
  relabel-H′ {p} {q} {a} {b} pq ab (no a≢p) (no a≢q) _ (yes ≡.refl) with FinP.<-cmp a p
  ... | tri< a<p _ _ =
    -- (c5) at a < p < q.
    trans (from-conj pq (axiom (c5 a<p (rc pq))))
          (trans (refl′ (≡.sym (Hs-< a<p))) (refl′ (≡.cong₂ Hs (≡.sym (τ-o p q a a≢p a≢q)) (≡.sym (τ-q p q (<⇒≢′ pq))))))
  ... | tri≈ _ a≡p _ = ⊥-elim (a≢p a≡p)
  ... | tri> _ _ p<a =
    -- p < a < q: X_pq H_aq X_pq = X_pa H_pa X_pa = Hs a p.
    trans core (trans (refl′ (≡.sym (Hs-> p<a))) (refl′ (≡.cong₂ Hs (≡.sym (τ-o p q a a≢p a≢q)) (≡.sym (τ-q p q (<⇒≢′ pq))))))
    where
    ab′ = rc ab
    Xpq = X p q pq
    Xpa = X p a p<a
    Xaq = X a q ab
    Hpa = H p a p<a
    -- (c4): H_aq = X_pa H_pq X_pa; (c5): H_pq = X_aq H_pa X_aq.
    h1 : H a q ab ≈ Xpa • H p q pq • Xpa
    h1 = conj-X′ p<a (axiom (c4 p<a ab′))
    h2 : H p q pq ≈ Xaq • Hpa • Xaq
    h2 = conj-X′ ab (axiom (c5 p<a ab′))
    -- (c2): X_aq X_pa = X_pa X_pq, and its inverse X_pa X_aq = X_pq X_pa.
    x2 : Xaq • Xpa ≈ Xpa • Xpq
    x2 = axiom (c2 p<a ab′)
    x2′ : Xpa • Xaq ≈ Xpq • Xpa
    x2′ = begin
      Xpa • Xaq                                   ≈⟨ sym left-unit ⟩
      ε • Xpa • Xaq                               ≈⟨ cleft sym (X-X pq) ⟩
      (Xpq • Xpq) • Xpa • Xaq                     ≈⟨ cright cright sym right-unit ⟩
      (Xpq • Xpq) • Xpa • Xaq • ε                 ≈⟨ cright cright cright sym (X-X p<a) ⟩
      (Xpq • Xpq) • Xpa • Xaq • (Xpa • Xpa)       ≈⟨ by-assoc auto ⟩
      Xpq • (Xpq • Xpa) • (Xaq • Xpa) • Xpa       ≈⟨ cright cright cleft x2 ⟩
      Xpq • (Xpq • Xpa) • (Xpa • Xpq) • Xpa       ≈⟨ by-assoc auto ⟩
      Xpq • Xpq • (Xpa • Xpa) • Xpq • Xpa         ≈⟨ cright cright cleft X-X p<a ⟩
      Xpq • Xpq • ε • Xpq • Xpa                   ≈⟨ cright cright left-unit ⟩
      Xpq • Xpq • Xpq • Xpa                       ≈⟨ cright (trans (sym assoc) (cleft X-X pq)) ⟩
      Xpq • ε • Xpa                               ≈⟨ cright left-unit ⟩
      Xpq • Xpa                                   ∎
    core : Xpq • H a q ab • Xpq ≈ Xpa • Hpa • Xpa
    core = begin
      Xpq • H a q ab • Xpq                        ≈⟨ cright cleft h1 ⟩
      Xpq • (Xpa • H p q pq • Xpa) • Xpq          ≈⟨ cright cleft cright cleft h2 ⟩
      Xpq • (Xpa • (Xaq • Hpa • Xaq) • Xpa) • Xpq ≈⟨ by-assoc auto ⟩
      Xpq • (Xpa • Xaq) • Hpa • (Xaq • Xpa) • Xpq ≈⟨ cright cong x2′ (cright cleft x2) ⟩
      Xpq • (Xpq • Xpa) • Hpa • (Xpa • Xpq) • Xpq ≈⟨ by-assoc auto ⟩
      (Xpq • Xpq) • Xpa • Hpa • Xpa • (Xpq • Xpq) ≈⟨ cong (X-X pq) (cright cright cright X-X pq) ⟩
      ε • Xpa • Hpa • Xpa • ε                     ≈⟨ trans left-unit (by-assoc auto) ⟩
      Xpa • Hpa • Xpa                             ∎
  -- a, b both apart from p, q.
  relabel-H′ {p} {q} {a} {b} pq ab (no a≢p) (no a≢q) (no b≢p) (no b≢q) =
    trans (conj-apart (H-gen a b ab) pq (apart-XH pq ab a≢p a≢q b≢p b≢q))
          (trans (refl′ (≡.sym (Hs-< ab))) (refl′ (≡.cong₂ Hs (≡.sym (τ-o p q a a≢p a≢q)) (≡.sym (τ-o p q b b≢p b≢q)))))
  -- a = p and b = p cannot both hold, nor a = p and b = p.
  relabel-H′ {p} {q} {a} {b} pq ab (yes ≡.refl) _ (yes ≡.refl) (no _) = ⊥-elim (<⇒≢′ ab ≡.refl)
  relabel-H′ {p} {q} {a} {b} pq ab (no _) (yes ≡.refl) (yes ≡.refl) _ = ⊥-elim (<⇒≢′ (FinP.<-trans (rc pq) (rc ab)) ≡.refl)


relabel-H : ∀ (pq : p < q) {a b} (ab : a < b) → X p q pq • H a b ab • X p q pq ≈ Hs (τ p q a) (τ p q b)
relabel-H {p = p} {q} pq {a} {b} ab = relabel-H′ pq ab (a FinP.≟ p) (a FinP.≟ q) (b FinP.≟ p) (b FinP.≟ q)

-- X, in increasing order: X_[p,q] X_[a,b] X_[p,q] = Xs (τ a) (τ b).
private
  relabel-X′ : ∀ {p q a b} (pq : p < q) (ab : a < b) → Dec (a ≡ p) → Dec (a ≡ q) → Dec (b ≡ p) → Dec (b ≡ q) →
               X p q pq • X a b ab • X p q pq ≈ Xs (τ p q a) (τ p q b)
  relabel-X′ {p} {q} {a} {b} pq ab (yes ≡.refl) _ _ (yes ≡.refl) = begin
    X′ • X′ • X′            ≈⟨ trans (sym assoc) (cleft X-X pq) ⟩
    ε • X′                  ≈⟨ left-unit ⟩
    X′                      ≈⟨ refl′ (≡.sym (Xs-> pq)) ⟩
    Xs q p                  ≈⟨ refl′ (≡.cong₂ Xs (≡.sym (τ-p p q)) (≡.sym (τ-q p q (<⇒≢′ pq)))) ⟩
    Xs (τ p q p) (τ p q q)  ∎
    where X′ = X p q pq
  relabel-X′ {p} {q} {a} {b} pq ab (yes ≡.refl) _ _ (no b≢q) with FinP.<-cmp q b
  ... | tri< q<b _ _ =
    trans (sym (conj-X′ pq (axiom (c2 pq q<b))))
          (trans (refl′ (≡.sym (Xs-< q<b))) (refl′ (≡.cong₂ Xs (≡.sym (τ-p p q)) (≡.sym (τ-o p q b (>⇒≢′ ab) b≢q)))))
  ... | tri≈ _ q≡b _ = ⊥-elim (b≢q (≡.sym q≡b))
  ... | tri> _ _ b<q =
    trans core (trans (refl′ (≡.sym (Xs-> b<q))) (refl′ (≡.cong₂ Xs (≡.sym (τ-p p q)) (≡.sym (τ-o p q b (>⇒≢′ ab) b≢q)))))
    where
    ab′ = rc ab
    Xpq = X p q pq
    Xbq = X b q b<q
    Xpb = X p b ab
    -- (c3): X_pq = X_bq X_pb X_bq; (c2): X_pq = X_pb X_bq X_pb.
    e3 : Xpq ≈ Xbq • Xpb • Xbq
    e3 = conj-X′ b<q (axiom (c3 ab′ b<q))
    e2 : Xpq ≈ Xpb • Xbq • Xpb
    e2 = conj-X ab (axiom (c2 ab′ b<q))
    core : Xpq • Xpb • Xpq ≈ Xbq
    core = begin
      Xpq • Xpb • Xpq                             ≈⟨ cong e2 (cright e2) ⟩
      (Xpb • Xbq • Xpb) • Xpb • (Xpb • Xbq • Xpb) ≈⟨ by-assoc auto ⟩
      Xpb • Xbq • (Xpb • Xpb) • Xpb • Xbq • Xpb   ≈⟨ cright cright cleft X-X ab ⟩
      Xpb • Xbq • ε • Xpb • Xbq • Xpb             ≈⟨ cright cright left-unit ⟩
      Xpb • Xbq • Xpb • Xbq • Xpb                 ≈⟨ by-assoc auto ⟩
      Xpb • (Xbq • Xpb • Xbq) • Xpb               ≈⟨ cright cleft sym e3 ⟩
      Xpb • Xpq • Xpb                             ≈⟨ cright cleft e2 ⟩
      Xpb • (Xpb • Xbq • Xpb) • Xpb               ≈⟨ by-assoc auto ⟩
      (Xpb • Xpb) • Xbq • (Xpb • Xpb)             ≈⟨ cong (X-X ab) (cright X-X ab) ⟩
      ε • Xbq • ε                                 ≈⟨ trans left-unit right-unit ⟩
      Xbq                                         ∎
  relabel-X′ {p} {q} {a} {b} pq ab (no a≢p) (yes ≡.refl) _ _ =
    trans (sym (conj-X pq (axiom (c2 (rc pq) (rc ab)))))
          (trans (refl′ (≡.sym (Xs-< (FinP.<-trans (rc pq) (rc ab)))))
                 (refl′ (≡.cong₂ Xs (≡.sym (τ-q p q (<⇒≢′ pq))) (≡.sym (τ-o p q b (>⇒≢′ (FinP.<-trans (rc pq) (rc ab))) (>⇒≢′ ab))))))
  relabel-X′ {p} {q} {a} {b} pq ab (no a≢p) (no a≢q) (yes ≡.refl) _ =
    trans (sym (conj-X′ pq (axiom (c3 (rc ab) (rc pq)))))
          (trans (refl′ (≡.sym (Xs-< (FinP.<-trans (rc ab) (rc pq)))))
                 (refl′ (≡.cong₂ Xs (≡.sym (τ-o p q a a≢p a≢q)) (≡.sym (τ-p p q)))))
  relabel-X′ {p} {q} {a} {b} pq ab (no a≢p) (no a≢q) _ (yes ≡.refl) with FinP.<-cmp a p
  ... | tri< a<p _ _ =
    trans (sym (conj-X pq (axiom (c3 a<p (rc pq)))))
          (trans (refl′ (≡.sym (Xs-< a<p))) (refl′ (≡.cong₂ Xs (≡.sym (τ-o p q a a≢p a≢q)) (≡.sym (τ-q p q (<⇒≢′ pq))))))
  ... | tri≈ _ a≡p _ = ⊥-elim (a≢p a≡p)
  ... | tri> _ _ p<a =
    trans core (trans (refl′ (≡.sym (Xs-> p<a))) (refl′ (≡.cong₂ Xs (≡.sym (τ-o p q a a≢p a≢q)) (≡.sym (τ-q p q (<⇒≢′ pq))))))
    where
    Xpq = X p q pq
    Xpa = X p a p<a
    Xaq = X a q ab
    core : Xpq • Xaq • Xpq ≈ Xpa
    core = begin
      Xpq • Xaq • Xpq             ≈⟨ sym assoc ⟩
      (Xpq • Xaq) • Xpq           ≈⟨ cleft axiom (c3 p<a (rc ab)) ⟩
      (Xaq • Xpa) • Xpq           ≈⟨ assoc ⟩
      Xaq • Xpa • Xpq             ≈⟨ sym assoc ⟩
      (Xaq • Xpa) • Xpq           ≈⟨ cleft axiom (c2 p<a (rc ab)) ⟩
      (Xpa • Xpq) • Xpq           ≈⟨ assoc ⟩
      Xpa • Xpq • Xpq             ≈⟨ cright X-X pq ⟩
      Xpa • ε                     ≈⟨ right-unit ⟩
      Xpa                         ∎
  relabel-X′ {p} {q} {a} {b} pq ab (no a≢p) (no a≢q) (no b≢p) (no b≢q) =
    trans (conj-apart (X-gen a b ab) pq
             (((a≢p ∘ ≡.sym) ∷ (b≢p ∘ ≡.sym) ∷ []) ∷ ((a≢q ∘ ≡.sym) ∷ (b≢q ∘ ≡.sym) ∷ []) ∷ []))
          (trans (refl′ (≡.sym (Xs-< ab))) (refl′ (≡.cong₂ Xs (≡.sym (τ-o p q a a≢p a≢q)) (≡.sym (τ-o p q b b≢p b≢q)))))
  relabel-X′ pq ab (yes ≡.refl) _ (yes ≡.refl) (no _) = ⊥-elim (<⇒≢′ ab ≡.refl)
  relabel-X′ pq ab (no _) (yes ≡.refl) (yes ≡.refl) _ = ⊥-elim (<⇒≢′ (FinP.<-trans (rc pq) (rc ab)) ≡.refl)

relabel-X : ∀ (pq : p < q) {a b} (ab : a < b) → X p q pq • X a b ab • X p q pq ≈ Xs (τ p q a) (τ p q b)
relabel-X {p = p} {q} pq {a} {b} ab = relabel-X′ pq ab (a FinP.≟ p) (a FinP.≟ q) (b FinP.≟ p) (b FinP.≟ q)

-- τ is an involution, so injective.
τ-τ : ∀ (p q x : Fin n) → p ≢ q → τ p q (τ p q x) ≡ x
τ-τ p q x p≢q = go (x FinP.≟ p) (x FinP.≟ q)
  where
  go : Dec (x ≡ p) → Dec (x ≡ q) → τ p q (τ p q x) ≡ x
  go (yes x≡p) _ = ≡.trans (≡.cong (λ y → τ p q (τ p q y)) x≡p)
                     (≡.trans (≡.cong (τ p q) (τ-p p q)) (≡.trans (τ-q p q p≢q) (≡.sym x≡p)))
  go (no x≢p) (yes x≡q) = ≡.trans (≡.cong (λ y → τ p q (τ p q y)) x≡q)
                            (≡.trans (≡.cong (τ p q) (τ-q p q p≢q)) (≡.trans (τ-p p q) (≡.sym x≡q)))
  go (no x≢p) (no x≢q) = ≡.trans (≡.cong (τ p q) (τ-o p q x x≢p x≢q)) (τ-o p q x x≢p x≢q)

τ-inj : ∀ (p q : Fin n) → p ≢ q → ∀ {x y} → τ p q x ≡ τ p q y → x ≡ y
τ-inj p q p≢q {x} {y} e = ≡.trans (≡.sym (τ-τ p q x p≢q)) (≡.trans (≡.cong (τ p q) e) (τ-τ p q y p≢q))

-- Conjugation distributes over •.
conj-• : ∀ .(pq : p < q) (u v : Word (Gen n)) →
         X p q pq • (u • v) • X p q pq ≈ (X p q pq • u • X p q pq) • (X p q pq • v • X p q pq)
conj-• pq u v = sym (begin
  (X′ • u • X′) • (X′ • v • X′)       ≈⟨ assoc ⟩
  X′ • (u • X′) • (X′ • v • X′)       ≈⟨ cright assoc ⟩
  X′ • u • X′ • (X′ • v • X′)         ≈⟨ cright cright sym assoc ⟩
  X′ • u • (X′ • X′) • v • X′         ≈⟨ cright cright cleft X-X pq ⟩
  X′ • u • ε • v • X′                 ≈⟨ cright cright left-unit ⟩
  X′ • u • v • X′                     ≈⟨ cright sym assoc ⟩
  X′ • (u • v) • X′                   ∎)
  where X′ = X _ _ pq

-- Symmetric words, in either order.
relabel-Xs : ∀ (pq : p < q) {a b} → a ≢ b → X p q pq • Xs a b • X p q pq ≈ Xs (τ p q a) (τ p q b)
relabel-Xs {p = p} {q} pq {a} {b} a≢b = by-order a≢b
  (λ lt → trans (cright cleft refl′ (Xs-< lt)) (relabel-X pq (rc lt)))
  (λ gt → trans (cright cleft refl′ (Xs-> gt))
             (trans (relabel-X pq (rc gt)) (Xs-sym (λ e → a≢b (τ-inj p q (<⇒≢′ pq) (≡.sym e))))))

relabel-Hs : ∀ (pq : p < q) {a b} → a ≢ b → X p q pq • Hs a b • X p q pq ≈ Hs (τ p q a) (τ p q b)
relabel-Hs {p = p} {q} pq {a} {b} a≢b = by-order a≢b
  (λ lt → trans (cright cleft refl′ (Hs-< lt)) (relabel-H pq (rc lt)))
  (λ gt → begin
     X′ • Hs a b • X′                                   ≈⟨ cright cleft refl′ (Hs-> gt) ⟩
     X′ • (X b a gt • H b a gt • X b a gt) • X′         ≈⟨ conj-• pq (X b a gt) (H b a gt • X b a gt) ⟩
     (X′ • X b a gt • X′) • (X′ • (H b a gt • X b a gt) • X′)
                                                        ≈⟨ cright conj-• pq (H b a gt) (X b a gt) ⟩
     (X′ • X b a gt • X′) • (X′ • H b a gt • X′) • (X′ • X b a gt • X′)
                                                        ≈⟨ cong (relabel-X pq (rc gt)) (cong (relabel-H pq (rc gt)) (relabel-X pq (rc gt))) ⟩
     Xs (τ p q b) (τ p q a) • Hs (τ p q b) (τ p q a) • Xs (τ p q b) (τ p q a)
                                                        ≈⟨ sym (Hs-flip τb≢τa) ⟩
     Hs (τ p q a) (τ p q b)                             ∎)
  where
  X′ = X p q pq
  τb≢τa : τ p q b ≢ τ p q a
  τb≢τa e = a≢b (≡.sym (τ-inj p q (<⇒≢′ pq) e))
