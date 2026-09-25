------------------------------------------------------------------------
-- Presentations of groups
--
-- Telescopes of transpositions
--
-- Definition E.1's word carries the basis vectors 0, 1, 3, 2 to four
-- given indices, and the proof of Figure 10's (71) needs the same
-- thing for six.  Both are the same construction, so here it is once,
-- over a *plan*: a list of pairs (target index , numeral).
--
--     ρ []            v  =  v
--     ρ ((x , k) ∷ p) v  =  (x , ρ p k) applied to ρ p v
--
-- Each step transposes its target with wherever the rest of the plan
-- sends its numeral, so `ρ p` carries each numeral of the plan to its
-- target; and the same transpositions in the other order undo it,
--
--     P []            v  =  v
--     P ((x , k) ∷ p) v  =  P p ((x , ρ p k) applied to v)  ,
--
-- which is what the word itself does.  `P p ∘ ρ p = id` needs nothing
-- but that a transposition is an involution; it is the *other* half —
-- that ρ really does send each numeral to its own target — that needs
-- the plan to have distinct targets and distinct numerals.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Telescope where

open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ ; _<_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)

open import Examples.Groups.Real-Clifford+CH.Encoding using (τ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Sigma
  using (τ-i ; τ-o ; τ-invol ; τ-<)

------------------------------------------------------------------------
-- Plans

Plan : Set
Plan = List (ℕ × ℕ)

-- Where the plan sends a numeral.
ρ : Plan → ℕ → ℕ
ρ []             v = v
ρ ((x , k) ∷ xs) v = τ x (ρ xs k) (ρ xs v)

-- And the same transpositions in the other order, which is what the
-- word built from the plan does.
P : Plan → ℕ → ℕ
P []             v = v
P ((x , k) ∷ xs) v = P xs (τ x (ρ xs k) v)

ρ-P : ∀ (xs : Plan) (v : ℕ) → P xs (ρ xs v) ≡ v
ρ-P []             v = Eq.refl
ρ-P ((x , k) ∷ xs) v =
  Eq.trans (Eq.cong (P xs) (τ-invol x (ρ xs k) (ρ xs v))) (ρ-P xs v)

ρ-inj : ∀ (xs : Plan) {u v : ℕ} → ρ xs u ≡ ρ xs v → u ≡ v
ρ-inj xs {u} {v} e =
  Eq.trans (Eq.sym (ρ-P xs u)) (Eq.trans (Eq.cong (P xs) e) (ρ-P xs v))

------------------------------------------------------------------------
-- Good plans

data _∈_ : ℕ × ℕ → Plan → Set where
  here  : ∀ {p xs}   → p ∈ (p ∷ xs)
  there : ∀ {p q xs} → p ∈ xs → p ∈ (q ∷ xs)

-- Distinct targets and distinct numerals.
data Ok : Plan → Set where
  nil  : Ok []
  cons : ∀ {x k xs} →
         (∀ {y j} → (y , j) ∈ xs → (x ≢ y) × (k ≢ j)) →
         Ok xs → Ok ((x , k) ∷ xs)

-- Each numeral lands on its target: the step that places it does so,
-- and every later step leaves it alone, since ρ is injective and the
-- numerals differ.
ρ-img : ∀ {xs : Plan} → Ok xs → ∀ {x k : ℕ} → (x , k) ∈ xs → ρ xs k ≡ x
ρ-img {_ ∷ ys} (cons h ok) {x} {k} here = τ-i x (ρ ys k)
ρ-img {(y , j) ∷ ys} (cons h ok) {x} {k} (there mem) =
  -- `τ` unfolds to an `if`, so this is a `subst` and not a `cong`:
  -- `τ y (ρ ys j) _` is not a neutral application to match against.
  Eq.subst (λ z → τ y (ρ ys j) z ≡ x) (Eq.sym rec)
           (τ-o y (ρ ys j) x (λ e → proj₁ (h mem) (Eq.sym e)) off)
  where
  rec : ρ ys k ≡ x
  rec = ρ-img {ys} ok {x} {k} mem

  off : x ≢ ρ ys j
  off e = proj₂ (h mem) (Eq.sym (ρ-inj ys (Eq.trans rec e)))

-- Hence the word's permutation sends each target to its numeral.
P-img : ∀ {xs : Plan} → Ok xs → ∀ {x k : ℕ} → (x , k) ∈ xs → P xs x ≡ k
P-img {xs} ok mem =
  Eq.trans (Eq.cong (P xs) (Eq.sym (ρ-img ok mem))) (ρ-P xs _)

------------------------------------------------------------------------
-- Bounds

Bounded : ∀ (N : ℕ) → Plan → Set
Bounded N xs = ∀ {x k : ℕ} → (x , k) ∈ xs → (x < N) × (k < N)

ρ-< : ∀ {N : ℕ} (xs : Plan) → Bounded N xs →
      ∀ {v : ℕ} → v < N → ρ xs v < N
ρ-< []             bd lt = lt
ρ-< ((x , k) ∷ ys) bd lt =
  τ-< x (ρ ys k) (ρ ys _) (proj₁ (bd here))
      (ρ-< ys (λ mem → bd (there mem)) (proj₂ (bd here)))
      (ρ-< ys (λ mem → bd (there mem)) lt)
