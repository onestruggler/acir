------------------------------------------------------------------------
-- Presentations of groups
--
-- Irreducible path-sums, and every path-sum reduces to one
--
-- Proposition 3.2 (Amy, QPL 2018) says that every sequence of rewrites
-- "terminates with an irreducible path-sum".  PathSum.Anywhere proves
-- that every rewrite sequence is finite (⟶ᵍ-SN).  This module proves
-- the other half, constructively: whether some rule applies to a
-- path-sum is decidable (step?).  So every path-sum reduces to an
-- irreducible one (normal-form), and irreducibility is decidable
-- (irreducible?).  With ⟶ᵍ-SN, any rewrite sequence can be continued
-- until it stops, and it stops at an irreducible path-sum.
--
-- The rules are those of PathSum.Anywhere: [Elim], [ω] and [HH] with
-- Z₂-linear quotients, at any path variable.  "Irreducible" is
-- relative to them: [Case], and the rules with quotients that are not
-- Z₂-linear, are not formalised.  Deciding whether a rule applies is
-- a finite search.  It tries every path variable to eliminate, checks
-- the premises coefficient by coefficient over all 2^(n+m) monomials,
-- and tries every candidate linear form (c , S) and, for [HH], every
-- substituted variable.  That takes exponential time.  The paper's
-- claim that rules are matched, and path-sums normalised, in
-- polynomial time is not formalised.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Anywhere.Match (M : ℕ) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (any?; all?)
open import Data.Fin.Subset using (Subset; inside; outside)
open import Data.Fin.Subset.Properties using (anySubset?)
open import Data.Integer.Base using (ℤ; +_; _-_)
open import Data.Integer.Divisibility.Signed using (_∣?_)
open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using ([]; _∷_)
open import Function.Base using (case_of_)
open import Relation.Nullary.Decidable using
  (Dec; yes; no; map′; _×?_; _⊎?_; _→?_)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base
open import PathSum.Order M using (pow)
open import PathSum.Polynomial
open import PathSum.Reduction M using (_⟶_; elim; ω; hh; ¼; ½)
open import PathSum.Reorder using (front; NoVar-front)
open import PathSum.Anywhere M using
  (_⟶ᵍ_; _⟶ᵍ*_; plain; at; εᵍ; _◅ᵍ_; SN; sn; ⟶ᵍ-SN)

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- Finite search

-- A statement about every subset, or every monomial, is decided by
-- trying each one; so is the existence of a Boolean with a property.

allSubset? : ∀ {k} {P : Subset k → Set} →
             (∀ s → Dec (P s)) → Dec (∀ s → P s)
allSubset? {zero}  {P} P? = map′ to from (P? [])
  where
  to : P [] → ∀ s → P s
  to p [] = p

  from : (∀ s → P s) → P []
  from all = all []
allSubset? {suc k} {P} P? =
  map′ to from (allSubset? (λ s → P? (inside ∷ s)) ×?
                allSubset? (λ s → P? (outside ∷ s)))
  where
  to : (∀ s → P (inside ∷ s)) × (∀ s → P (outside ∷ s)) → ∀ s → P s
  to (pᵢ , pₒ) (inside  ∷ s) = pᵢ s
  to (pᵢ , pₒ) (outside ∷ s) = pₒ s

  from : (∀ s → P s) → (∀ s → P (inside ∷ s)) × (∀ s → P (outside ∷ s))
  from all = (λ s → all (inside ∷ s)) , (λ s → all (outside ∷ s))

allMon? : {P : Mon n m → Set} → (∀ γ → Dec (P γ)) → Dec (∀ γ → P γ)
allMon? P? = map′ (λ h γ → h (proj₁ γ) (proj₂ γ)) (λ h α β → h (α , β))
  (allSubset? (λ α → allSubset? (λ β → P? (α , β))))

anyMon? : {P : Mon n m → Set} → (∀ γ → Dec (P γ)) → Dec (∃ P)
anyMon? {P = P} P? =
  map′ to from (anySubset? (λ α → anySubset? (λ β → P? (α , β))))
  where
  to : (∃ λ α → ∃ λ β → P (α , β)) → ∃ P
  to (α , β , p) = (α , β) , p

  from : ∃ P → ∃ λ α → ∃ λ β → P (α , β)
  from ((α , β) , p) = α , β , p

anyBool? : {P : Bool → Set} → (∀ b → Dec (P b)) → Dec (∃ P)
anyBool? {P} P? = map′ to from (P? true ⊎? P? false)
  where
  to : P true ⊎ P false → ∃ P
  to (inj₁ p) = true , p
  to (inj₂ p) = false , p

  from : ∃ P → P true ⊎ P false
  from (true  , p) = inj₁ p
  from (false , p) = inj₂ p

-- The premises of the rules are coefficient-wise, hence decidable.

infix 4 _≈?[_]_

_≈?[_]_ : (P : Poly n m) (c : ℤ) (Q : Poly n m) → Dec (P ≈[ c ] Q)
P ≈?[ c ] Q = allMon? (λ γ → c ∣? (P γ - Q γ))

NoVar? : (c : ℤ) (v : Var n m) (P : Poly n m) → Dec (NoVar c v P)
NoVar? c v P = allMon? (λ γ → (v ∈ᵐ? γ) →? (c ∣? P γ))


------------------------------------------------------------------------
-- Whether a head rule applies

-- The premises of the head rules, other than the normalisation they
-- consume: y₀ is absent from the outputs, and the quotient of the
-- phase by y₀ is 0 ([Elim]), ¼ + ½(c ⊕ ⨁S) ([ω]), or ½(c ⊕ ⨁S) with
-- a path variable in S ([HH]).

Internal₀ : PathSum n k (suc m) → Set
Internal₀ {n} ξ = ∀ (w : Fin n) → NoVar (+ 2) y₀ (out ξ w)

ElimQ : PathSum n k (suc m) → Set
ElimQ ξ = head-part (phase ξ) ≈[ pow M ] 0ᴾ

ΩQ : PathSum n k (suc m) → Set
ΩQ {n = n} {m = m} ξ = ∃ λ (c : Bool) → ∃ λ (S : Mon n m) →
  head-part (phase ξ) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ liftXor c S))

HHQ : PathSum n k (suc m) → Set
HHQ {n = n} {m = m} ξ = ∃ λ (i : Fin m) → ∃ λ (c : Bool) →
  ∃ λ (S : Mon n m) →
  y[ i ] ∈ᵐ S × head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ liftXor c S)

Internal₀? : (ξ : PathSum n k (suc m)) → Dec (Internal₀ ξ)
Internal₀? ξ = all? (λ w → NoVar? (+ 2) y₀ (out ξ w))

ElimQ? : (ξ : PathSum n k (suc m)) → Dec (ElimQ ξ)
ElimQ? ξ = head-part (phase ξ) ≈?[ pow M ] 0ᴾ

ΩQ? : (ξ : PathSum n k (suc m)) → Dec (ΩQ ξ)
ΩQ? ξ = anyBool? (λ c → anyMon? (λ S →
  head-part (phase ξ) ≈?[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ liftXor c S))))

HHQ? : (ξ : PathSum n k (suc m)) → Dec (HHQ ξ)
HHQ? ξ = any? (λ i → anyBool? (λ c → anyMon? (λ S →
  (y[ i ] ∈ᵐ? S) ×?
  (head-part (phase ξ) ≈?[ pow M ] (½ ·ᴾ liftXor c S)))))

-- Some head rule applies to ξ.

HeadStep : PathSum n k m → Set
HeadStep {n} ξ = ∃ λ k′ → ∃ λ m′ → ∃ λ (ζ : PathSum n k′ m′) → ξ ⟶ ζ

-- Every head rule needs y₀ internal; which of the others can apply
-- depends on the normalisation: [HH] always, [ω] from 1, [Elim]
-- from 2.

private
  internal₀ : {ξ : PathSum n k (suc m)} {ζ : PathSum n k′ m′} →
              ξ ⟶ ζ → Internal₀ ξ
  internal₀ (elim _ _ o)       = o
  internal₀ (ω _ _ _ _ o)      = o
  internal₀ (hh _ _ _ _ _ _ o) = o

  stuck₀ : {ξ : PathSum n 0 (suc m)} {ζ : PathSum n k′ m′} →
           ¬ HHQ ξ → ¬ (ξ ⟶ ζ)
  stuck₀ ¬h (hh _ i c S i∈S eq _) = ¬h (i , c , S , i∈S , eq)

  stuck₁ : {ξ : PathSum n 1 (suc m)} {ζ : PathSum n k′ m′} →
           ¬ ΩQ ξ → ¬ HHQ ξ → ¬ (ξ ⟶ ζ)
  stuck₁ ¬ω ¬h (ω _ c S eq _)          = ¬ω (c , S , eq)
  stuck₁ ¬ω ¬h (hh _ i c S i∈S eq _)   = ¬h (i , c , S , i∈S , eq)

  stuck₂ : {ξ : PathSum n (suc (suc k)) (suc m)} {ζ : PathSum n k′ m′} →
           ¬ ElimQ ξ → ¬ ΩQ ξ → ¬ HHQ ξ → ¬ (ξ ⟶ ζ)
  stuck₂ ¬e ¬ω ¬h (elim _ eq _)          = ¬e eq
  stuck₂ ¬e ¬ω ¬h (ω _ c S eq _)         = ¬ω (c , S , eq)
  stuck₂ ¬e ¬ω ¬h (hh _ i c S i∈S eq _)  = ¬h (i , c , S , i∈S , eq)

  by-norm : (ξ : PathSum n k (suc m)) → Internal₀ ξ → ¬ HHQ ξ →
            Dec (HeadStep ξ)
  by-norm {k = zero}        ξ o ¬h = no λ (_ , _ , _ , s) → stuck₀ ¬h s
  by-norm {k = suc zero}    ξ o ¬h = case ΩQ? ξ of λ where
    (yes (c , S , eq)) → yes (_ , _ , _ , ω ξ c S eq o)
    (no ¬ω)            → no λ (_ , _ , _ , s) → stuck₁ ¬ω ¬h s
  by-norm {k = suc (suc k)} ξ o ¬h = case ΩQ? ξ of λ where
    (yes (c , S , eq)) → yes (_ , _ , _ , ω ξ c S eq o)
    (no ¬ω)            → case ElimQ? ξ of λ where
      (yes eq) → yes (_ , _ , _ , elim ξ eq o)
      (no ¬e)  → no λ (_ , _ , _ , s) → stuck₂ ¬e ¬ω ¬h s

head? : (ξ : PathSum n k (suc m)) → Dec (HeadStep ξ)
head? ξ = case Internal₀? ξ of λ where
  (no ¬o) → no λ (_ , _ , _ , s) → ¬o (internal₀ s)
  (yes o) → case HHQ? ξ of λ where
    (yes (i , c , S , i∈S , eq)) → yes (_ , _ , _ , hh ξ i c S i∈S eq o)
    (no ¬h)                      → by-norm ξ o ¬h


------------------------------------------------------------------------
-- Irreducible path-sums

-- No rule applies at any path variable.

Irreducible : PathSum n k m → Set
Irreducible {n} ξ = ∀ {k′ m′} {ζ : PathSum n k′ m′} → ¬ (ξ ⟶ᵍ ζ)

-- A head step on ξ is one on front zero ξ: its premises are the same,
-- coefficient by coefficient.

private
  at-zero : {ξ : PathSum n k (suc m)} {ζ : PathSum n k′ m′} →
            ξ ⟶ ζ → HeadStep (front zero ξ)
  at-zero {ξ = ξ} (elim _ eq o) =
    _ , _ , _ , elim (front zero ξ) eq (λ w → NoVar-front zero (out ξ w) (o w))
  at-zero {ξ = ξ} (ω _ c S eq o) =
    _ , _ , _ ,
    ω (front zero ξ) c S eq (λ w → NoVar-front zero (out ξ w) (o w))
  at-zero {ξ = ξ} (hh _ i c S i∈S eq o) =
    _ , _ , _ ,
    hh (front zero ξ) i c S i∈S eq
       (λ w → NoVar-front zero (out ξ w) (o w))

  -- If no head rule applies at any variable moved to the front, no
  -- rule applies at all.
  none : (ξ : PathSum n k (suc m)) →
         ¬ (∃ λ j → HeadStep (front j ξ)) → Irreducible ξ
  none ξ ¬any (plain s) = ¬any (zero , at-zero s)
  none ξ ¬any (at j s)  = ¬any (j , _ , _ , _ , s)

-- Either some rule applies, or none does: try a head rule at every
-- path variable moved to the front.

step? : (ξ : PathSum n k m) →
        (∃ λ k′ → ∃ λ m′ → ∃ λ (ζ : PathSum n k′ m′) → ξ ⟶ᵍ ζ) ⊎
        Irreducible ξ
step? {m = zero}  ξ = inj₂ λ { (plain ()) }
step? {m = suc m} ξ with any? (λ j → head? (front j ξ))
... | yes (j , _ , _ , _ , s) = inj₁ (_ , _ , _ , at j s)
... | no ¬any                 = inj₂ (none ξ ¬any)

irreducible? : (ξ : PathSum n k m) → Dec (Irreducible ξ)
irreducible? ξ with step? ξ
... | inj₁ (_ , _ , _ , s) = no λ irr → irr s
... | inj₂ irr             = yes irr


------------------------------------------------------------------------
-- Proposition 3.2: every path-sum reduces to an irreducible one

-- Rewrite while a rule applies; the recursion is on strong
-- normalisation, so it stops.

normal-form : (ξ : PathSum n k m) →
              ∃ λ k′ → ∃ λ m′ → ∃ λ (ξ′ : PathSum n k′ m′) →
                (ξ ⟶ᵍ* ξ′) × Irreducible ξ′
normal-form {n = n} ξ = go ξ (⟶ᵍ-SN ξ)
  where
  NF : ∀ {k m} → PathSum n k m → Set
  NF ξ = ∃ λ k′ → ∃ λ m′ → ∃ λ (ξ′ : PathSum n k′ m′) →
           (ξ ⟶ᵍ* ξ′) × Irreducible ξ′

  go : ∀ {k m} (ξ : PathSum n k m) → SN _⟶ᵍ_ ξ → NF ξ
  go ξ (sn next) with step? ξ
  ... | inj₂ irr              = _ , _ , ξ , εᵍ , irr
  ... | inj₁ (_ , _ , ζ , s) with go ζ (next s)
  ...   | k′ , m′ , ξ′ , steps , irr = k′ , m′ , ξ′ , s ◅ᵍ steps , irr
