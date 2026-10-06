------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 2 without [Case], and a certificate that only [Case] applies
--
-- Section 3.2 of Amy's paper (QPL 2018) says that the rule [Case] "is
-- a specific case distinction needed to prove" a two-qubit Clifford+T
-- identity.  To state "needed", this module separates [Case] from the
-- other three rules inside PathSum.Full's calculus _⟶ᶠ_ -- all four
-- rules of figure 2, at any internal path variable or pair, with
-- Boolean-valued quotients -- without changing that calculus.
--
-- * NoCaseᶠ s says that a step s of _⟶ᶠ_ is an [Elim], an [ω] or an
--   [HH] step, at whatever variable it acts.  ξ ⟶⁻ ζ is a step of that
--   kind: figure 2 without [Case], in the same generality (any
--   quotient, any variable, any renumbering _⟶ᶠ_ allows); _⟶⁻*_ is its
--   chains.  The linear calculus of PathSum.Anywhere is part of it
--   (⟶ᵍ⇒⟶⁻).
-- * Stuck⁻ ξ says that no such step applies to ξ.  Then every step of
--   _⟶ᶠ_ from ξ is a [Case] (only-case), no chain without [Case] from ξ
--   reaches a path-sum without path variables (NeedsCase,
--   stuck⁻-chains), and every chain of _⟶ᶠ_ from ξ that does begins
--   with a [Case] step (CaseFirst, case-first).
-- * A certificate of Stuck⁻, in the manner of PathSum.Full.Obstruction.
--   [Elim], [ω] and [HH] at the head all need the coefficient of y₀ to
--   be a multiple of ¼ and, for any input x_i, the coefficient of
--   x_i y₀ to be a multiple of ½ (the constant ¼ of [ω] sits at the
--   monomial 1, not at x_i): necessary.  This is the first half of
--   Obstruction's condition, without the alternative that [Case]
--   allows.  Its failure at ξ, at every front j ξ and at every
--   front j′ (front j ξ) -- the four shapes a step of _⟶ᶠ_ takes are
--   head rules at these -- is decidable by computing two coefficients
--   at each (certificate?), and certifies Stuck⁻ (stuck⁻!).  It is
--   sufficient, not necessary, and ignores whether y₀ is internal.
-- * The certificate reads coefficients modulo divisors of 2^M, so it
--   passes along a congruence of phases (certificate-≈): it can be
--   computed on a literal path-sum and carried to one congruent to it
--   whose coefficients are expensive to compute.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Full.WithoutCase (M : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty using () renaming (⊥ to ⊥ᵉ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (all?)
open import Data.Fin.Subset using (Subset; ⊥; ⁅_⁆; inside; outside; _∈_)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆; ∉⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; ∣-refl; ∣-trans; ∣m∣n⇒∣m+n; ∣m⇒∣-m; ∣m+n∣n⇒∣m; ∣m⇒∣m*n)
open import Data.Nat.Base using (zero; suc; _∸_; s≤s; z≤n)
open import Data.Nat.Properties using (m∸n≤m; ∸-monoʳ-≤)
open import Data.Product.Base using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base using (_∷_; insertAt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; cong; subst)
open import Relation.Nullary.Decidable using
  (Dec; yes; no; True; toWitness; _×?_; ¬?)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Base using (PathSum; phase)
open import PathSum.Order M using (pow; pow-∣)
open import PathSum.Polynomial using (Mon; Poly; 1ᵐ; κ; _≈[_]_; _≟ᵐ_)
open import PathSum.Polynomial.Properties using (i∣0)
open import PathSum.Reduction M using (_⟶_; elim; ω; hh; ¼; ½)
open import PathSum.Reduction.General M using
  (_⟶ᴳ_; elimᴳ; ωᴳ; hhᴳ; caseᴳ; ⟶⇒⟶ᴳ)
open import PathSum.Reorder using (front; frontᴾ)
open import PathSum.Anywhere M using (plain; at; _⟶ᵍ_)
open import PathSum.Full M using (_⟶ᶠ_; _⟶ᶠ*_; εᶠ; _◅ᶠ_)

private
  variable
    n k m k′ m′ k″ m″ : ℕ


------------------------------------------------------------------------
-- The steps that are not [Case]

-- The rule a step of the head calculus uses, and then a step of
-- _⟶ᶠ_, whose four shapes each wrap one head step.

NoCaseᴳ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᴳ ζ → Set
NoCaseᴳ (elimᴳ _ _ _)                   = ⊤
NoCaseᴳ (ωᴳ _ _ _ _ _)                  = ⊤
NoCaseᴳ (hhᴳ _ _ _ _ _ _ _)             = ⊤
NoCaseᴳ (caseᴳ _ _ _ _ _ _ _ _ _ _ _ _) = ⊥ᵉ

NoCaseᶠ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᶠ ζ → Set
NoCaseᶠ (plain (plain s)) = NoCaseᴳ s
NoCaseᶠ (plain (at _ s))  = NoCaseᴳ s
NoCaseᶠ (at _ (plain s))  = NoCaseᴳ s
NoCaseᶠ (at _ (at _ s))   = NoCaseᴳ s

-- Figure 2 without [Case]: [Elim], [ω] and [HH], Boolean-valued
-- quotients, any internal variable.

infix  4 _⟶⁻_ _⟶⁻*_
infixr 5 _◅⁻_

_⟶⁻_ : PathSum n k m → PathSum n k′ m′ → Set
ξ ⟶⁻ ζ = Σ (ξ ⟶ᶠ ζ) NoCaseᶠ

data _⟶⁻*_ {n : ℕ} : ∀ {k m k′ m′} →
                     PathSum n k m → PathSum n k′ m′ → Set where
  ε⁻   : ∀ {k m} {ξ : PathSum n k m} → ξ ⟶⁻* ξ
  _◅⁻_ : ∀ {k m k′ m′ k″ m″} {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
         {χ : PathSum n k″ m″} → ξ ⟶⁻ ζ → ζ ⟶⁻* χ → ξ ⟶⁻* χ

-- Its chains are chains of _⟶ᶠ_.

⟶⁻*⇒⟶ᶠ* : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
          ξ ⟶⁻* ζ → ξ ⟶ᶠ* ζ
⟶⁻*⇒⟶ᶠ* ε⁻              = εᶠ
⟶⁻*⇒⟶ᶠ* ((s , _) ◅⁻ ss) = s ◅ᶠ ⟶⁻*⇒⟶ᶠ* ss

-- The linear rules of PathSum.Reduction, at any variable, are steps
-- of it: none of them is a [Case].

private
  linear-no-case : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
                   (s : ξ ⟶ ζ) → NoCaseᴳ (⟶⇒⟶ᴳ s)
  linear-no-case (elim _ _ _)         = tt
  linear-no-case (ω _ _ _ _ _)        = tt
  linear-no-case (hh _ _ _ _ _ _ _)   = tt

⟶ᵍ⇒⟶⁻ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᵍ ζ → ξ ⟶⁻ ζ
⟶ᵍ⇒⟶⁻ (plain s) = plain (plain (⟶⇒⟶ᴳ s)) , linear-no-case s
⟶ᵍ⇒⟶⁻ (at j s)  = at j (plain (⟶⇒⟶ᴳ s)) , linear-no-case s


------------------------------------------------------------------------
-- Stuck without [Case]

Stuck⁻ : PathSum n k m → Set
Stuck⁻ {n} ξ = ∀ {k′ m′} {ζ : PathSum n k′ m′} → ¬ (ξ ⟶⁻ ζ)

-- Then every rule of figure 2 that applies is a [Case] ...

only-case : {ξ : PathSum n k m} → Stuck⁻ ξ →
            ∀ {k′ m′} {ζ : PathSum n k′ m′} (s : ξ ⟶ᶠ ζ) → ¬ NoCaseᶠ s
only-case stuck s nc = stuck (s , nc)

-- ... no chain without [Case] gets rid of the path variables ...

NeedsCase : PathSum n k m → Set
NeedsCase {n} ξ = ∀ {k′} {ζ : PathSum n k′ 0} → ¬ (ξ ⟶⁻* ζ)

stuck⁻-chains : (ξ : PathSum n k (suc m)) → Stuck⁻ ξ → NeedsCase ξ
stuck⁻-chains ξ stuck (s ◅⁻ _) = stuck s

-- ... and every chain of figure 2 that does begins with a [Case].

CaseFirst : PathSum n k m → Set
CaseFirst {n} ξ =
  ∀ {k′} {ζ : PathSum n k′ 0} → ξ ⟶ᶠ* ζ →
  ∃ λ k″ → ∃ λ m″ → ∃ λ (χ : PathSum n k″ m″) →
    Σ (ξ ⟶ᶠ χ) (λ s → ¬ NoCaseᶠ s) × (χ ⟶ᶠ* ζ)

case-first : (ξ : PathSum n k (suc m)) → Stuck⁻ ξ → CaseFirst ξ
case-first ξ stuck (s ◅ᶠ ss) =
  _ , _ , _ , (s , only-case stuck s) , ss


------------------------------------------------------------------------
-- Two coefficients

-- For a path-sum with at least one path variable: the coefficients of
-- y₀ and of x_i y₀.

coef₀ : PathSum n k (suc m) → ℤ
coef₀ χ = phase χ (⊥ , inside ∷ ⊥)

coefˣ : Fin n → PathSum n k (suc m) → ℤ
coefˣ i χ = phase χ (⁅ i ⁆ , inside ∷ ⊥)

-- What [Elim], [ω] and [HH] at the head imply of them.

Necessary : Fin n → PathSum n k (suc m) → Set
Necessary i χ = pow (M ∸ 2) ∣ coef₀ χ × pow (M ∸ 1) ∣ coefˣ i χ

necessary? : (i : Fin n) (χ : PathSum n k (suc m)) → Dec (Necessary i χ)
necessary? i χ = (pow (M ∸ 2) ∣? coef₀ χ) ×? (pow (M ∸ 1) ∣? coefˣ i χ)


------------------------------------------------------------------------
-- Divisibility

private
  ¼∣N : pow (M ∸ 2) ∣ pow M
  ¼∣N = pow-∣ (m∸n≤m M 2)

  ½∣N : pow (M ∸ 1) ∣ pow M
  ½∣N = pow-∣ (m∸n≤m M 1)

  ¼∣½ : pow (M ∸ 2) ∣ pow (M ∸ 1)
  ¼∣½ = pow-∣ (∸-monoʳ-≤ M (s≤s z≤n))

  -- p ∣ u from 2^M ∣ u - v, when p divides 2^M and v.

  by-diff : ∀ {p u v} → p ∣ pow M → pow M ∣ (u - v) → p ∣ v → p ∣ u
  by-diff p∣N e p∣v = ∣m+n∣n⇒∣m (∣-trans p∣N e) (∣m⇒∣-m p∣v)

  -- A constant polynomial is c at the monomial 1 and 0 elsewhere.

  if-∣ : ∀ {p c} (b : Bool) → p ∣ c → p ∣ (if b then c else 0ℤ)
  if-∣ true  p∣c = p∣c
  if-∣ false _   = i∣0

  κ-∣ : ∀ {p c} (γ : Mon n m) → p ∣ c → p ∣ κ c γ
  κ-∣ γ p∣c = if-∣ _ p∣c

  κ-off : (c : ℤ) {γ : Mon n m} → ¬ (γ ≡ 1ᵐ) → κ c γ ≡ 0ℤ
  κ-off c {γ} ne with γ ≟ᵐ 1ᵐ
  ... | yes p = contradiction p ne
  ... | no _  = refl

  -- x_i alone is not the monomial 1.

  xᵢ≢1 : (i : Fin n) → ¬ ((⁅ i ⁆ , ⊥) ≡ 1ᵐ {n} {m})
  xᵢ≢1 i eq = ∉⊥ (subst (i ∈_) (cong proj₁ eq) (x∈⁅x⁆ i))

  ½-mul : ∀ s → pow (M ∸ 1) ∣ (½ * s)
  ½-mul s = ∣m⇒∣m*n s ∣-refl

  ¼½-mul : ∀ s → pow (M ∸ 2) ∣ (½ * s)
  ¼½-mul s = ∣m⇒∣m*n s ¼∣½


------------------------------------------------------------------------
-- Every head rule but [Case] implies the condition

-- Each premise read at the monomial 1 of the quotient, which is y₀ of
-- the phase, and at x_i.

necessary : (i : Fin n) (χ : PathSum n k (suc m)) {ζ : PathSum n k′ m′}
            (s : χ ⟶ᴳ ζ) → NoCaseᴳ s → Necessary i χ
necessary i χ (elimᴳ _ eq _) _ =
  by-diff ¼∣N (eq (⊥ , ⊥)) i∣0 , by-diff ½∣N (eq (⁅ i ⁆ , ⊥)) i∣0
necessary {n = n} {m = m} i χ (ωᴳ _ Q _ eq _) _ =
  by-diff ¼∣N (eq (⊥ , ⊥))
    (∣m∣n⇒∣m+n (κ-∣ {n = n} {m = m} (⊥ , ⊥) ∣-refl)
               (¼½-mul (Q (⊥ , ⊥)))) ,
  by-diff ½∣N (eq (⁅ i ⁆ , ⊥))
    (∣m∣n⇒∣m+n
      (subst (pow (M ∸ 1) ∣_)
             (sym (κ-off ¼ {⁅ i ⁆ , ⊥} (xᵢ≢1 {m = m} i))) i∣0)
      (½-mul (Q (⁅ i ⁆ , ⊥))))
necessary i χ (hhᴳ _ _ _ _ _ eq _) _ =
  by-diff ¼∣N (eq (⊥ , ⊥)) (¼½-mul _) ,
  by-diff ½∣N (eq (⁅ i ⁆ , ⊥)) (½-mul _)
necessary i χ (caseᴳ _ _ _ _ _ _ _ _ _ _ _ _) ()


------------------------------------------------------------------------
-- The certificate

-- The condition fails at ξ, at each single renumbering and at each
-- double one: wherever a head rule of a step of _⟶ᶠ_ would act.

Certificate : Fin n → PathSum n k (suc m) → Set
Certificate {m = m} i ξ =
  ¬ Necessary i ξ ×
  (∀ (j : Fin (suc m)) → ¬ Necessary i (front j ξ)) ×
  (∀ (j j′ : Fin (suc m)) → ¬ Necessary i (front j′ (front j ξ)))

certificate? : (i : Fin n) (ξ : PathSum n k (suc m)) →
               Dec (Certificate i ξ)
certificate? i ξ =
  ¬? (necessary? i ξ) ×?
  all? (λ j → ¬? (necessary? i (front j ξ))) ×?
  all? (λ j → all? (λ j′ → ¬? (necessary? i (front j′ (front j ξ)))))

certificate⇒stuck⁻ : (i : Fin n) (ξ : PathSum n k (suc m)) →
                     Certificate i ξ → Stuck⁻ ξ
certificate⇒stuck⁻ i ξ (c₀ , c₁ , c₂) (plain (plain s) , nc) =
  c₀ (necessary i ξ s nc)
certificate⇒stuck⁻ i ξ (c₀ , c₁ , c₂) (plain (at j s) , nc) =
  c₁ j (necessary i (front j ξ) s nc)
certificate⇒stuck⁻ i ξ (c₀ , c₁ , c₂) (at j (plain s) , nc) =
  c₁ j (necessary i (front j ξ) s nc)
certificate⇒stuck⁻ i ξ (c₀ , c₁ , c₂) (at j (at j′ s) , nc) =
  c₂ j j′ (necessary i (front j′ (front j ξ)) s nc)

-- With the certificate computed.

stuck⁻! : (i : Fin n) (ξ : PathSum n k (suc m)) →
          {True (certificate? i ξ)} → Stuck⁻ ξ
stuck⁻! i ξ {t} =
  certificate⇒stuck⁻ i ξ (toWitness {a? = certificate? i ξ} t)


------------------------------------------------------------------------
-- Along a congruence of phases

-- Renumbering reads a coefficient of the original, so it keeps a
-- coefficient-wise congruence.

front-≈ : (j : Fin (suc m)) {c : ℤ} {P Q : Poly n (suc m)} →
          P ≈[ c ] Q → frontᴾ j P ≈[ c ] frontᴾ j Q
front-≈ j eq (α , b ∷ s) = eq (α , insertAt s j b)

-- The condition reads coefficients modulo divisors of 2^M.

necessary-≈ : (i : Fin n) (χ : PathSum n k (suc m))
              (χ′ : PathSum n k′ (suc m)) →
              phase χ ≈[ pow M ] phase χ′ →
              Necessary i χ′ → Necessary i χ
necessary-≈ i χ χ′ eq (d₀ , dˣ) =
  by-diff ¼∣N (eq (⊥ , inside ∷ ⊥)) d₀ ,
  by-diff ½∣N (eq (⁅ i ⁆ , inside ∷ ⊥)) dˣ

-- A certificate for ζ is one for every ξ whose phase is congruent to
-- ζ's.

certificate-≈ : (i : Fin n) (ζ : PathSum n k (suc m))
                (ξ : PathSum n k′ (suc m)) →
                phase ζ ≈[ pow M ] phase ξ →
                Certificate i ζ → Certificate i ξ
certificate-≈ i ζ ξ eq (c₀ , c₁ , c₂) =
  (λ nξ → c₀ (necessary-≈ i ζ ξ eq nξ)) ,
  (λ j nξ → c₁ j (necessary-≈ i (front j ζ) (front j ξ)
                    (front-≈ j eq) nξ)) ,
  (λ j j′ nξ → c₂ j j′ (necessary-≈ i (front j′ (front j ζ))
                          (front j′ (front j ξ))
                          (front-≈ j′ (front-≈ j eq)) nξ))
