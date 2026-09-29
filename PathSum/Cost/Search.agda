------------------------------------------------------------------------
-- Presentations of groups
--
-- Whether some rule applies at some path variable, on the sparse
-- representation (for Amy, QPL 2018, proposition 3.2)
--
-- PathSum.Anywhere.Match decides whether a rule of PathSum.Anywhere
-- applies to a path-sum by a finite search over all 2^(n+m)
-- coefficients and all candidate linear forms: exponentially many
-- steps.  Here the same question is answered on the sparse
-- representation, in the cost model of PathSum.Cost, with the sparse
-- rules of PathSum.Cost.Rules.
--
--  * tryAtᶜ d k j R tries the rules at y_j in the order of
--    PathSum.Anywhere.Match.head?: [HH]; then [ω] if the normalisation
--    k is at least 1; then [Elim] if k is at least 2.  Each test of k
--    costs a step.  It returns the new normalisation and
--    representation of the first rule that applies.
--  * searchᶜ d k R tries y_0, y_1, ..., y_m in turn and stops at the
--    first variable where a rule applies (PathSum.Cost.firstJustᶜ).
--
-- Proved:
--
--  * search-sound: what the search returns is a step of the dense
--    path-sum.  For any ξ that R represents whose terms have order at
--    most d (d ≥ 2, for [ω]), ξ ⟶ᵍ ξ′ for a ξ′ with the new
--    normalisation that the new representation represents, whose
--    terms again have order at most d; and the new representation is
--    canonical (search-canonical);
--  * search-complete: when the search finds nothing, every path-sum
--    that a canonical R represents is irreducible
--    (PathSum.Anywhere.Match.Irreducible: no rule of PathSum.Anywhere
--    applies at any variable).  A step of _⟶ᵍ_ is a head rule on ξ
--    or on front j ξ.  Its premises are those of the rule at y_j, and
--    the sparse matchers are complete there on canonical
--    representations (PathSum.Cost.Complete), so the rule would have
--    been found at y_j.  A step at the head of ξ itself is a step at
--    y_0: its premises are the same, coefficient by coefficient, by
--    definition;
--  * cost-searchᶜ: on a canonical representation with n inputs and
--    m + 1 path variables, at most (m + 1)(3 + 276 (n + m + 3)^(3d+3))
--    steps.  Each variable costs at most three rules, and on a
--    canonical representation each rule costs at most
--    92 (n + m + 3)^(3d+3) (PathSum.Cost.Rules.canonical-cost).
--
-- Costs are counted in the cost model of PathSum.Cost: a cost model,
-- not a machine model; nothing is claimed about Turing machines or
-- complexity classes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Search (M : ℕ) where

open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (inside)
open import Data.Integer.Base using (ℤ; +_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (_∷_; here; insertAt; removeAt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import PathSum.Anywhere M using (_⟶ᵍ_; plain; at)
open import PathSum.Anywhere.Match M using (Irreducible)
open import PathSum.Base using (PathSum; phase; out)
open import PathSum.Cost
open import PathSum.Cost.Canon M using (Canonical; Ordᵀ)
open import PathSum.Cost.Complete M using
  (elimˢ-complete; ωˢ-complete; hhˢ-complete)
open import PathSum.Cost.Rules M using
  (elimˢ; ωˢ; hhˢ; elimˢ-sound; ωˢ-sound; hhˢ-sound; elimˢ-canonical;
   ωˢ-canonical; hhˢ-canonical; Bᴿ; canonical-cost)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using
  (Mon; Poly; y[_]; _∈ᵐ_; κ; 0ᴾ; _+ᴾ_; _·ᴾ_; _≈[_]_; NoVar; liftXor)
open import PathSum.Reduction M using
  (_⟶_; elim; ω; hh; elim-reduct; ω-reduct; hh-reduct; ¼; ½)
open import PathSum.Reorder using (front; frontᴾ; _/ʸ_)
open import PathSum.Size.Sparse M using (Rep; terms; Represents)

import Data.Nat.Properties as ℕ
import Data.Vec.Properties as Vec

open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

private
  variable
    d k k′ n m : ℕ


------------------------------------------------------------------------
-- The rules at one variable

-- [Elim] consumes two units of normalisation, [ω] one, [HH] none; k is
-- the normalisation left.

afterElim : ℕ → Maybe (Rep n m) → Cost (Maybe (ℕ × Rep n m))
afterElim k (just R′) = pure (just (k , R′))
afterElim k nothing   = pure nothing

afterω : ℕ → ℕ → Fin (suc m) → Rep n (suc m) →
         Maybe (Bool × Mon n m × Rep n m) → Cost (Maybe (ℕ × Rep n m))
afterω d k       j R (just (_ , _ , R′)) = pure (just (k , R′))
afterω d zero    j R nothing             = step nothing
afterω d (suc k) j R nothing             = tick >> (elimˢ d j R >>= afterElim k)

afterHH : ℕ → ℕ → Fin (suc m) → Rep n (suc m) →
          Maybe (Fin m × Bool × Mon n m × Rep n m) →
          Cost (Maybe (ℕ × Rep n m))
afterHH d k       j R (just (_ , _ , _ , R′)) = pure (just (k , R′))
afterHH d zero    j R nothing                 = step nothing
afterHH d (suc k) j R nothing                 =
  tick >> (ωˢ d j R >>= afterω d k j R)

tryAtᶜ : ℕ → ℕ → Fin (suc m) → Rep n (suc m) → Cost (Maybe (ℕ × Rep n m))
tryAtᶜ d k j R = hhˢ d j R >>= afterHH d k j R

-- Every variable in turn.

searchᶜ : ℕ → ℕ → Rep n (suc m) → Cost (Maybe (ℕ × Rep n m))
searchᶜ d k R = firstJustᶜ (λ j → tryAtᶜ d k j R)


------------------------------------------------------------------------
-- Soundness

-- A step found: ξ steps to a path-sum with the new normalisation, which
-- the new representation represents, keeping the order bound.

Stepped : ℕ → PathSum n k (suc m) → ℕ → Rep n m → Set
Stepped {n} {m = m} d ξ k′ R′ =
  Σ (PathSum n k′ m) λ ξ′ →
    (ξ ⟶ᵍ ξ′) × Represents ξ′ R′ × Ordᵀ d (terms R′)

afterElim-sound : (d k : ℕ) (j : Fin (suc m))
                  (ξ : PathSum n (suc (suc k)) (suc m)) (R : Rep n (suc m)) →
                  Represents ξ R → Ordᵀ d (terms R) →
                  (r : Maybe (Rep n m)) → value (elimˢ d j R) ≡ r →
                  ∀ {k′ R′} → value (afterElim k r) ≡ just (k′ , R′) →
                  Stepped d ξ k′ R′
afterElim-sound d k j ξ R rp ord (just R₁) e refl =
  elim-reduct (front j ξ) , elimˢ-sound d j ξ R rp ord e
afterElim-sound d k j ξ R rp ord nothing   e ()

afterω-sound : (d : ℕ) → 2 ≤ d → (k : ℕ) (j : Fin (suc m))
               (ξ : PathSum n (suc k) (suc m)) (R : Rep n (suc m)) →
               Represents ξ R → Ordᵀ d (terms R) →
               (r : Maybe (Bool × Mon n m × Rep n m)) →
               value (ωˢ d j R) ≡ r →
               ∀ {k′ R′} → value (afterω d k j R r) ≡ just (k′ , R′) →
               Stepped d ξ k′ R′
afterω-sound d 2≤d k       j ξ R rp ord (just (c , S , R₁)) e refl =
  ω-reduct (front j ξ) c S , ωˢ-sound d 2≤d j ξ R rp ord e
afterω-sound d 2≤d zero    j ξ R rp ord nothing e ()
afterω-sound d 2≤d (suc k) j ξ R rp ord nothing e eq =
  afterElim-sound d k j ξ R rp ord (value (elimˢ d j R)) refl eq

afterHH-sound : (d : ℕ) → 2 ≤ d → (k : ℕ) (j : Fin (suc m))
                (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) →
                Represents ξ R → Ordᵀ d (terms R) →
                (r : Maybe (Fin m × Bool × Mon n m × Rep n m)) →
                value (hhˢ d j R) ≡ r →
                ∀ {k′ R′} → value (afterHH d k j R r) ≡ just (k′ , R′) →
                Stepped d ξ k′ R′
afterHH-sound d 2≤d k       j ξ R rp ord (just (i , c , S , R₁)) e refl =
  hh-reduct (front j ξ) i c S , hhˢ-sound d j ξ R rp ord e
afterHH-sound d 2≤d zero    j ξ R rp ord nothing e ()
afterHH-sound d 2≤d (suc k) j ξ R rp ord nothing e eq =
  afterω-sound d 2≤d k j ξ R rp ord (value (ωˢ d j R)) refl eq

tryAt-sound : (d : ℕ) → 2 ≤ d → (k : ℕ) (j : Fin (suc m))
              (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) →
              Represents ξ R → Ordᵀ d (terms R) →
              ∀ {k′ R′} → value (tryAtᶜ d k j R) ≡ just (k′ , R′) →
              Stepped d ξ k′ R′
tryAt-sound d 2≤d k j ξ R rp ord eq =
  afterHH-sound d 2≤d k j ξ R rp ord (value (hhˢ d j R)) refl eq

search-sound : (d : ℕ) → 2 ≤ d → (ξ : PathSum n k (suc m))
               (R : Rep n (suc m)) → Represents ξ R → Ordᵀ d (terms R) →
               ∀ {k′ R′} → value (searchᶜ d k R) ≡ just (k′ , R′) →
               Stepped d ξ k′ R′
search-sound {k = k} d 2≤d ξ R rp ord eq =
  tryAt-sound d 2≤d k (proj₁ found) ξ R rp ord (proj₂ found)
  where
  found = firstJustᶜ-just (λ j → tryAtᶜ d k j R) eq

-- The representation returned is canonical, whatever the input.

afterElim-canonical : (d k : ℕ) (j : Fin (suc m)) (R : Rep n (suc m))
                      (r : Maybe (Rep n m)) → value (elimˢ d j R) ≡ r →
                      ∀ {k′ R′} → value (afterElim k r) ≡ just (k′ , R′) →
                      Canonical d (terms R′)
afterElim-canonical d k j R (just R₁) e refl = elimˢ-canonical d j R e
afterElim-canonical d k j R nothing   e ()

afterω-canonical : (d k : ℕ) (j : Fin (suc m)) (R : Rep n (suc m))
                   (r : Maybe (Bool × Mon n m × Rep n m)) →
                   value (ωˢ d j R) ≡ r →
                   ∀ {k′ R′} → value (afterω d k j R r) ≡ just (k′ , R′) →
                   Canonical d (terms R′)
afterω-canonical d k       j R (just (c , S , R₁)) e refl =
  ωˢ-canonical d j R e
afterω-canonical d zero    j R nothing e ()
afterω-canonical d (suc k) j R nothing e eq =
  afterElim-canonical d k j R (value (elimˢ d j R)) refl eq

afterHH-canonical : (d k : ℕ) (j : Fin (suc m)) (R : Rep n (suc m))
                    (r : Maybe (Fin m × Bool × Mon n m × Rep n m)) →
                    value (hhˢ d j R) ≡ r →
                    ∀ {k′ R′} → value (afterHH d k j R r) ≡ just (k′ , R′) →
                    Canonical d (terms R′)
afterHH-canonical d k       j R (just (i , c , S , R₁)) e refl =
  hhˢ-canonical d j R e
afterHH-canonical d zero    j R nothing e ()
afterHH-canonical d (suc k) j R nothing e eq =
  afterω-canonical d k j R (value (ωˢ d j R)) refl eq

search-canonical : (d k : ℕ) (R : Rep n (suc m)) →
                   ∀ {k′ R′} → value (searchᶜ d k R) ≡ just (k′ , R′) →
                   Canonical d (terms R′)
search-canonical d k R eq =
  afterHH-canonical d k (proj₁ found) R (value (hhˢ d (proj₁ found) R)) refl
                    (proj₂ found)
  where
  found = firstJustᶜ-just (λ j → tryAtᶜ d k j R) eq


------------------------------------------------------------------------
-- Completeness

-- When nothing is found at y_j, none of the rules tried applied.

private
  nothing≢just : ∀ {A : Set} {a : A} → nothing ≡ just a → ⊥
  nothing≢just ()

  afterElim-nothing : (k : ℕ) (r : Maybe (Rep n m)) →
                      value (afterElim k r) ≡ nothing → r ≡ nothing
  afterElim-nothing k (just _) ()
  afterElim-nothing k nothing  _ = refl

  afterω-nothing : (d k : ℕ) (j : Fin (suc m)) (R : Rep n (suc m))
                   (r : Maybe (Bool × Mon n m × Rep n m)) →
                   value (afterω d k j R r) ≡ nothing → r ≡ nothing
  afterω-nothing d k j R (just _) ()
  afterω-nothing d k j R nothing  _ = refl

  afterHH-nothing : (d k : ℕ) (j : Fin (suc m)) (R : Rep n (suc m))
                    (r : Maybe (Fin m × Bool × Mon n m × Rep n m)) →
                    value (afterHH d k j R r) ≡ nothing → r ≡ nothing
  afterHH-nothing d k j R (just _) ()
  afterHH-nothing d k j R nothing  _ = refl

tryAt-hh : (d k : ℕ) (j : Fin (suc m)) (R : Rep n (suc m)) →
           value (tryAtᶜ d k j R) ≡ nothing → value (hhˢ d j R) ≡ nothing
tryAt-hh d k j R eq = afterHH-nothing d k j R (value (hhˢ d j R)) eq

tryAt-ω : (d k : ℕ) (j : Fin (suc m)) (R : Rep n (suc m)) →
          value (tryAtᶜ d (suc k) j R) ≡ nothing → value (ωˢ d j R) ≡ nothing
tryAt-ω d k j R eq = go (value (hhˢ d j R)) eq
  where
  go : ∀ r → value (afterHH d (suc k) j R r) ≡ nothing →
       value (ωˢ d j R) ≡ nothing
  go (just _) ()
  go nothing  e = afterω-nothing d k j R (value (ωˢ d j R)) e

tryAt-elim : (d k : ℕ) (j : Fin (suc m)) (R : Rep n (suc m)) →
             value (tryAtᶜ d (suc (suc k)) j R) ≡ nothing →
             value (elimˢ d j R) ≡ nothing
tryAt-elim d k j R eq = go (value (hhˢ d j R)) eq
  where
  go′ : ∀ r → value (afterω d (suc k) j R r) ≡ nothing →
        value (elimˢ d j R) ≡ nothing
  go′ (just _) ()
  go′ nothing  e = afterElim-nothing k (value (elimˢ d j R)) e

  go : ∀ r → value (afterHH d (suc (suc k)) j R r) ≡ nothing →
       value (elimˢ d j R) ≡ nothing
  go (just _) ()
  go nothing  e = go′ (value (ωˢ d j R)) e

-- So, on a canonical representation, the premises of none of those
-- rules hold at y_j.

tryAt-no-hh : (d : ℕ) (j : Fin (suc m)) (ξ : PathSum n k (suc m))
              (R : Rep n (suc m)) → Represents ξ R → Canonical d (terms R) →
              value (tryAtᶜ d k j R) ≡ nothing →
              (i : Fin m) (c : Bool) (S : Mon n m) → y[ i ] ∈ᵐ S →
              (phase ξ /ʸ j) ≈[ pow M ] (½ ·ᴾ liftXor c S) →
              (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) → ⊥
tryAt-no-hh {k = k} d j ξ R rp can eq i c S i∈S e nv =
  nothing≢just (trans (sym (tryAt-hh d k j R eq))
    (proj₂ (hhˢ-complete d ξ R rp can j i c S i∈S e nv)))

tryAt-no-ω : (d : ℕ) (j : Fin (suc m)) (ξ : PathSum n (suc k) (suc m))
             (R : Rep n (suc m)) → Represents ξ R → Canonical d (terms R) →
             value (tryAtᶜ d (suc k) j R) ≡ nothing →
             (c : Bool) (S : Mon n m) →
             (phase ξ /ʸ j) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ liftXor c S)) →
             (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) → ⊥
tryAt-no-ω {k = k} d j ξ R rp can eq c S e nv =
  nothing≢just (trans (sym (tryAt-ω d k j R eq))
    (proj₂ (ωˢ-complete d ξ R rp can j c S e nv)))

tryAt-no-elim : (d : ℕ) (j : Fin (suc m))
                (ξ : PathSum n (suc (suc k)) (suc m)) (R : Rep n (suc m)) →
                Represents ξ R → Canonical d (terms R) →
                value (tryAtᶜ d (suc (suc k)) j R) ≡ nothing →
                (phase ξ /ʸ j) ≈[ pow M ] 0ᴾ →
                (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) → ⊥
tryAt-no-elim {k = k} d j ξ R rp can eq e nv =
  nothing≢just (trans (sym (tryAt-elim d k j R eq))
    (proj₂ (elimˢ-complete d ξ R rp can j e nv)))

-- The premise on the outputs of a head rule on front j ξ is that of
-- the rule at y_j of ξ.

NoVar-unfront : {c : ℤ} (j : Fin (suc m)) (P : Poly n (suc m)) →
                NoVar c y[ zero ] (frontᴾ j P) → NoVar c y[ j ] P
NoVar-unfront {c = c} j P h (α , β) j∈β =
  subst (c ∣_) (cong (λ β′ → P (α , β′))
    (trans (cong (insertAt (removeAt β j) j) (sym (Vec.[]=⇒lookup j∈β)))
           (Vec.insertAt-removeAt β j)))
    (h (α , inside ∷ removeAt β j) here)

-- If nothing is found at any variable, no rule applies at all.

nothing-irreducible : (d : ℕ) (ξ : PathSum n k (suc m))
                      (R : Rep n (suc m)) →
                      Represents ξ R → Canonical d (terms R) →
                      (∀ j → value (tryAtᶜ d k j R) ≡ nothing) →
                      Irreducible ξ
nothing-irreducible d ξ R rp can none (plain (elim _ e o)) =
  tryAt-no-elim d zero ξ R rp can (none zero) e o
nothing-irreducible d ξ R rp can none (plain (ω _ c S e o)) =
  tryAt-no-ω d zero ξ R rp can (none zero) c S e o
nothing-irreducible d ξ R rp can none (plain (hh _ i c S i∈S e o)) =
  tryAt-no-hh d zero ξ R rp can (none zero) i c S i∈S e o
nothing-irreducible d ξ R rp can none (at j (elim _ e o)) =
  tryAt-no-elim d j ξ R rp can (none j) e
    (λ w → NoVar-unfront j (out ξ w) (o w))
nothing-irreducible d ξ R rp can none (at j (ω _ c S e o)) =
  tryAt-no-ω d j ξ R rp can (none j) c S e
    (λ w → NoVar-unfront j (out ξ w) (o w))
nothing-irreducible d ξ R rp can none (at j (hh _ i c S i∈S e o)) =
  tryAt-no-hh d j ξ R rp can (none j) i c S i∈S e
    (λ w → NoVar-unfront j (out ξ w) (o w))

search-complete : (d : ℕ) (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) →
                  Represents ξ R → Canonical d (terms R) →
                  value (searchᶜ d k R) ≡ nothing → Irreducible ξ
search-complete {k = k} d ξ R rp can eq = nothing-irreducible d ξ R rp can
  (firstJustᶜ-nothing (λ j → tryAtᶜ d k j R) eq)


------------------------------------------------------------------------
-- Cost

-- At one variable: the rules tried, and a step per test of k.

private
  cost-afterElim : (k : ℕ) (r : Maybe (Rep n m)) → cost (afterElim k r) ≡ 0
  cost-afterElim k (just _) = refl
  cost-afterElim k nothing  = refl

cost-afterω : (d k : ℕ) (j : Fin (suc m)) (R : Rep n (suc m))
              (r : Maybe (Bool × Mon n m × Rep n m)) →
              cost (afterω d k j R r) ≤ suc (cost (elimˢ d j R))
cost-afterω d k       j R (just _) = z≤n
cost-afterω d zero    j R nothing  = s≤s z≤n
cost-afterω d (suc k) j R nothing  = s≤s (ℕ.≤-reflexive
  (trans (cong (λ z → cost (elimˢ d j R) + z)
               (cost-afterElim k (value (elimˢ d j R))))
         (ℕ.+-identityʳ (cost (elimˢ d j R)))))

cost-afterHH : (d k : ℕ) (j : Fin (suc m)) (R : Rep n (suc m))
               (r : Maybe (Fin m × Bool × Mon n m × Rep n m)) →
               cost (afterHH d k j R r) ≤
               suc (cost (ωˢ d j R) + suc (cost (elimˢ d j R)))
cost-afterHH d k       j R (just _) = z≤n
cost-afterHH d zero    j R nothing  = s≤s z≤n
cost-afterHH d (suc k) j R nothing  = s≤s (ℕ.+-monoʳ-≤ (cost (ωˢ d j R))
  (cost-afterω d k j R (value (ωˢ d j R))))

cost-tryAtᶜ : (d k : ℕ) (j : Fin (suc m)) (R : Rep n (suc m)) →
              cost (tryAtᶜ d k j R) ≤
              cost (hhˢ d j R) +
              suc (cost (ωˢ d j R) + suc (cost (elimˢ d j R)))
cost-tryAtᶜ d k j R = ℕ.+-monoʳ-≤ (cost (hhˢ d j R))
  (cost-afterHH d k j R (value (hhˢ d j R)))

-- On a canonical representation, with X = 92 (n + m + 3)^(3d+3) the
-- bound on one rule: at most 3X + 2 per variable.

ruleX : ℕ → ℕ → ℕ → ℕ
ruleX n m d = 92 * Bᴿ n m ^ (3 * d + 3)

tryBound : ℕ → ℕ → ℕ → ℕ
tryBound n m d = 2 + 3 * ruleX n m d

cost-tryAt-canonical : (d k : ℕ) (j : Fin (suc m)) (R : Rep n (suc m)) →
                       Canonical d (terms R) →
                       cost (tryAtᶜ d k j R) ≤ tryBound n m d
cost-tryAt-canonical {m} {n} d k j R can = ℕ.≤-trans (cost-tryAtᶜ d k j R)
  (ℕ.≤-trans (ℕ.+-mono-≤ hh≤ (s≤s (ℕ.+-mono-≤ ω≤ (s≤s el≤))))
             (ℕ.≤-reflexive (three X)))
  where
  X = ruleX n m d
  cc = canonical-cost d j R can
  el≤ = proj₁ cc
  ω≤  = proj₁ (proj₂ cc)
  hh≤ = proj₂ (proj₂ cc)

  three : ∀ X → X + suc (X + suc X) ≡ 2 + 3 * X
  three = solve 1 (λ X → X :+ (con 1 :+ (X :+ (con 1 :+ X))) :=
                         con 2 :+ con 3 :* X) refl

-- The whole search: at most m + 1 variables.

searchBound : ℕ → ℕ → ℕ → ℕ
searchBound n m d = suc m * suc (tryBound n m d)

cost-searchᶜ : (d k : ℕ) (R : Rep n (suc m)) → Canonical d (terms R) →
               cost (searchᶜ d k R) ≤ searchBound n m d
cost-searchᶜ d k R can = cost-firstJustᶜ (λ j → tryAtᶜ d k j R)
  (λ j → cost-tryAt-canonical d k j R can)
