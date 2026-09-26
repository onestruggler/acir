------------------------------------------------------------------------
-- Presentations of groups
--
-- A cheap certificate that no rule of figure 2 applies
--
-- PathSum.Full.Match decides whether any rule of figure 2 applies to a
-- path-sum, at any path variable or pair (irreducibleᶠ?).  The decision
-- is exact but expensive: at each of the m² double renumberings of a
-- path-sum with m path variables it computes a canonical quotient for
-- [ω], for [HH] at every y_i and for [Case], each folding over every
-- monomial, and compares it with the phase over all 2^(n+m)
-- monomials.  On the path-sum of section 4 of the paper (two inputs,
-- eight path variables) the check had not finished after 14 minutes
-- (PathSum.Examples.Incomplete).  This module gives a sufficient
-- condition instead, read off four coefficients of the phase, which
-- the type checker computes there in seconds.
--
-- Every head rule reads the quotient of the phase by y₀ -- the
-- coefficients of the monomials containing y₀ -- and asks it to be a
-- multiple of ¼ (numerator 2^(M-2)) plus a multiple of ½ (numerator
-- 2^(M-1)) of a polynomial with integer coefficients, modulo 2^M:
--
--   [Elim]  quotient ≡ 0;
--   [ω]     quotient ≡ ¼ + ½Q;
--   [HH]    quotient ≡ ½(y_i + Q);
--   [Case]  y₀-quarter ≡ ¼X + ½Q, y₁-quarter ≡ ¼(1 - X) + ½Q′,
--           y₀y₁-quarter ≡ ½.
--
-- So in every case the coefficient of the monomial y₀ is a multiple of
-- 2^(M-2).  In the first three the coefficient of x_i y₀, for any input
-- x_i, is a multiple of 2^(M-2+1) = 2^(M-1), since the constant ¼ of
-- [ω] sits at the monomial 1, not at x_i.  In [Case] the coefficient of
-- y₀y₁ is ½ and that of y₁ a multiple of 2^(M-2).  Necessary i χ says
-- the first of these, and either the second or the third, and
-- necessary proves that every head rule applying to χ implies it.
-- Its negation at every double renumbering front j′ (front j ξ) --
-- every choice of the variable a rule acts at,
-- and of its partner for [Case] -- is therefore a certificate of
-- Irreducibleᶠ ξ (obstructed⇒irreducible), decidable by computing four
-- coefficients at each of the (m+2)² renumberings (obstructed?), and
-- used by computing that decision (irreducible!).
--
-- The certificate is sufficient, not necessary: it ignores the side
-- condition that y₀ be internal, and every coefficient but four, so a
-- path-sum can be irreducible without being obstructed.  It is phrased
-- for path-sums with at least two path variables, which is where
-- [Case] can apply.
--
-- Two facts about irreducible path-sums close the module.  One without
-- path variables is irreducible, every rule removing one
-- (no-paths-irreducible); so the identity is a normal form.  And from
-- an irreducible path-sum with path variables no chain of rules
-- reaches one without (irreducible-stuck): the only chain is the empty
-- one.  Nothing here is about a particular path-sum; the instance is
-- PathSum.Examples.Incomplete, the paper's witness that normal forms
-- are not unique.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Full.Obstruction (M : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (all?)
open import Data.Fin.Subset using (Subset; ⊥; ⁅_⁆; inside; outside; _∈_)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆; ∉⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; ∣-refl; ∣-trans; ∣m∣n⇒∣m+n; ∣m⇒∣-m; ∣m+n∣n⇒∣m; ∣m⇒∣m*n)
open import Data.Nat.Base using (zero; suc; _∸_; s≤s; z≤n)
open import Data.Nat.Properties using (m∸n≤m; ∸-monoʳ-≤)
open import Data.Product.Base using (_×_; _,_; proj₁)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using (_∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; cong; subst)
open import Relation.Nullary.Decidable using
  (Dec; yes; no; True; toWitness; _×?_; _⊎?_; ¬?)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Base using (PathSum; phase)
open import PathSum.Order M using (pow; pow-∣)
open import PathSum.Polynomial using (Mon; 1ᵐ; κ; _≟ᵐ_)
open import PathSum.Polynomial.Properties using (i∣0)
open import PathSum.Reduction M using (¼; ½)
open import PathSum.Reduction.General M using
  (_⟶ᴳ_; elimᴳ; ωᴳ; hhᴳ; caseᴳ)
open import PathSum.Reorder using (front)
open import PathSum.Anywhere M using (plain)
open import PathSum.Full M using (_⟶ᶠ*_; _◅ᶠ_)
open import PathSum.Full.Match M using
  (HeadStepᴳ; Irreducibleᶠ; head⇒Irreducibleᶠ)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- Four coefficients

-- For a path-sum with at least two path variables: the coefficients of
-- y₀, of y₁, of y₀y₁, and of x_i y₀.

coef₀ coef₁ coef₀₁ : PathSum n k (suc (suc m)) → ℤ
coef₀  χ = phase χ (⊥ , inside  ∷ outside ∷ ⊥)
coef₁  χ = phase χ (⊥ , outside ∷ inside  ∷ ⊥)
coef₀₁ χ = phase χ (⊥ , inside  ∷ inside  ∷ ⊥)

coefˣ : Fin n → PathSum n k (suc (suc m)) → ℤ
coefˣ i χ = phase χ (⁅ i ⁆ , inside ∷ outside ∷ ⊥)

-- What a head step at χ implies of them.

Necessary : Fin n → PathSum n k (suc (suc m)) → Set
Necessary i χ =
  pow (M ∸ 2) ∣ coef₀ χ ×
  (pow (M ∸ 1) ∣ coefˣ i χ ⊎
   (pow M ∣ (coef₀₁ χ - ½) × pow (M ∸ 2) ∣ coef₁ χ))

necessary? : (i : Fin n) (χ : PathSum n k (suc (suc m))) →
             Dec (Necessary i χ)
necessary? i χ =
  (pow (M ∸ 2) ∣? coef₀ χ) ×?
  ((pow (M ∸ 1) ∣? coefˣ i χ) ⊎?
   ((pow M ∣? (coef₀₁ χ - ½)) ×? (pow (M ∸ 2) ∣? coef₁ χ)))


------------------------------------------------------------------------
-- Divisibility

private
  -- The quarter divides the half, and both divide 2^M.

  ¼∣½ : pow (M ∸ 2) ∣ pow (M ∸ 1)
  ¼∣½ = pow-∣ (∸-monoʳ-≤ M (s≤s z≤n))

  ¼∣N : pow (M ∸ 2) ∣ pow M
  ¼∣N = pow-∣ (m∸n≤m M 2)

  ½∣N : pow (M ∸ 1) ∣ pow M
  ½∣N = pow-∣ (m∸n≤m M 1)

  -- p ∣ u from 2^M ∣ u - v, when p divides 2^M and v.

  by-diff : ∀ {p u v} → p ∣ pow M → pow M ∣ (u - v) → p ∣ v → p ∣ u
  by-diff p∣N e p∣v = ∣m+n∣n⇒∣m (∣-trans p∣N e) (∣m⇒∣-m p∣v)

  -- A constant polynomial is c at the monomial 1 and 0 elsewhere.

  if-∣ : ∀ {p c} (b : Bool) → p ∣ c → p ∣ (if b then c else 0ℤ)
  if-∣ true  p∣c = p∣c
  if-∣ false _   = i∣0

  κ-∣ : ∀ {p c} (γ : Mon n m) → p ∣ c → p ∣ κ c γ
  κ-∣ γ p∣c = if-∣ _ p∣c

  κ-1ᵐ : (c : ℤ) → κ {n} {m} c 1ᵐ ≡ c
  κ-1ᵐ {n} {m} c with (1ᵐ {n} {m}) ≟ᵐ 1ᵐ
  ... | yes _ = refl
  ... | no ¬p = contradiction refl ¬p

  κ-off : (c : ℤ) {γ : Mon n m} → ¬ (γ ≡ 1ᵐ) → κ c γ ≡ 0ℤ
  κ-off c {γ} ne with γ ≟ᵐ 1ᵐ
  ... | yes p = contradiction p ne
  ... | no _  = refl

  -- x_i alone is not the monomial 1.

  xᵢ≢1 : (i : Fin n) → ¬ ((⁅ i ⁆ , ⊥) ≡ 1ᵐ {n} {m})
  xᵢ≢1 i eq = ∉⊥ (subst (i ∈_) (cong proj₁ eq) (x∈⁅x⁆ i))

  -- Multiples of the half and of the quarter.

  ½-mul : ∀ s → pow (M ∸ 1) ∣ (½ * s)
  ½-mul s = ∣m⇒∣m*n s ∣-refl

  ¼-mul : ∀ s → pow (M ∸ 2) ∣ (¼ * s)
  ¼-mul s = ∣m⇒∣m*n s ∣-refl

  ¼½-mul : ∀ s → pow (M ∸ 2) ∣ (½ * s)
  ¼½-mul s = ∣m⇒∣m*n s ¼∣½


------------------------------------------------------------------------
-- Every head rule implies the condition

-- Each rule's premise is read at the monomial 1 of the quotient, which
-- is y₀ (or y₀y₁, or y₁) of the phase, and for the first three rules
-- also at x_i.

necessary : (i : Fin n) (χ : PathSum n k (suc (suc m))) →
            HeadStepᴳ χ → Necessary i χ
necessary i χ (_ , _ , _ , elimᴳ _ eq _) =
  by-diff ¼∣N (eq (⊥ , ⊥)) i∣0 ,
  inj₁ (by-diff ½∣N (eq (⁅ i ⁆ , ⊥)) i∣0)
necessary {n = n} {m = m} i χ (_ , _ , _ , ωᴳ _ Q _ eq _) =
  by-diff ¼∣N (eq (⊥ , ⊥))
    (∣m∣n⇒∣m+n (κ-∣ {n = n} {m = suc m} (⊥ , ⊥) ∣-refl)
               (¼½-mul (Q (⊥ , ⊥)))) ,
  inj₁ (by-diff ½∣N (eq (⁅ i ⁆ , ⊥))
         (∣m∣n⇒∣m+n
           (subst (pow (M ∸ 1) ∣_)
                  (sym (κ-off ¼ {⁅ i ⁆ , ⊥} (xᵢ≢1 {m = suc m} i))) i∣0)
           (½-mul (Q (⁅ i ⁆ , ⊥)))))
necessary i χ (_ , _ , _ , hhᴳ _ i′ Q _ _ eq _) =
  by-diff ¼∣N (eq (⊥ , ⊥)) (¼½-mul _) ,
  inj₁ (by-diff ½∣N (eq (⁅ i ⁆ , ⊥)) (½-mul _))
necessary {n = n} {m = m} i χ
          (_ , _ , _ , caseᴳ _ X Q Q′ _ _ _ e₁₁ e₁₀ e₀₁ _ _) =
  by-diff ¼∣N (e₁₀ (⊥ , ⊥))
    (∣m∣n⇒∣m+n (¼-mul (X (⊥ , ⊥))) (¼½-mul (Q (⊥ , ⊥)))) ,
  inj₂ (subst (λ c → pow M ∣ (coef₀₁ χ - c)) (κ-1ᵐ {n} {m} ½) (e₁₁ (⊥ , ⊥)) ,
        by-diff ¼∣N (e₀₁ (⊥ , ⊥))
          (∣m∣n⇒∣m+n (¼-mul _) (¼½-mul (Q′ (⊥ , ⊥)))))


------------------------------------------------------------------------
-- The certificate

-- The condition fails at every double renumbering: whichever variable
-- a rule would act at, and whichever partner [Case] would take.

Obstructed : Fin n → PathSum n k (suc (suc m)) → Set
Obstructed {m = m} i ξ =
  ∀ (j j′ : Fin (suc (suc m))) → ¬ Necessary i (front j′ (front j ξ))

obstructed? : (i : Fin n) (ξ : PathSum n k (suc (suc m))) →
              Dec (Obstructed i ξ)
obstructed? i ξ =
  all? (λ j → all? (λ j′ → ¬? (necessary? i (front j′ (front j ξ)))))

obstructed⇒irreducible : (i : Fin n) (ξ : PathSum n k (suc (suc m))) →
                         Obstructed i ξ → Irreducibleᶠ ξ
obstructed⇒irreducible i ξ h = head⇒Irreducibleᶠ ξ (λ j j′ s →
  h j j′ (necessary i (front j′ (front j ξ)) s))

-- With the certificate computed.

irreducible! : (i : Fin n) (ξ : PathSum n k (suc (suc m))) →
               {True (obstructed? i ξ)} → Irreducibleᶠ ξ
irreducible! i ξ {t} =
  obstructed⇒irreducible i ξ (toWitness {a? = obstructed? i ξ} t)


------------------------------------------------------------------------
-- What irreducibility rules out

-- Every rule acts at a path variable, so a path-sum without any is
-- irreducible: the identity, for one, is a normal form.

no-paths-irreducible : (ξ : PathSum n k 0) → Irreducibleᶠ ξ
no-paths-irreducible ξ (plain (plain ()))

-- The only chain from an irreducible path-sum is the empty one, so if
-- it has path variables, no chain reaches a path-sum without.

irreducible-stuck : (ξ : PathSum n k (suc m)) → Irreducibleᶠ ξ →
                    ∀ {k′} {ζ : PathSum n k′ 0} → ¬ (ξ ⟶ᶠ* ζ)
irreducible-stuck ξ irr (s ◅ᶠ _) = irr s
