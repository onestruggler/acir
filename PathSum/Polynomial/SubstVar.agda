------------------------------------------------------------------------
-- Presentations of groups
--
-- Substituting one variable for another, with cheap coefficients
--
-- PathSum.Polynomial.subst substitutes the lifting of a Z₂-linear
-- form c ⊕ ⨁S for a variable v.  Its coefficient at a monomial γ is a
-- double sum over all monomials δ and β, collecting the terms of the
-- quotient P /ᵛ v at δ times those of the lifting at β, with δ ∪ β = γ.
-- That is the right definition for proofs, but on a closed polynomial
-- with n inputs and m path variables one coefficient costs 4^(n+m)
-- terms.  PathSum.Gauss substitutes this way when it reifies the
-- isometry restriction of section 4.1 (Amy, QPL 2018), so the
-- coefficients of a reified restriction do not compute in practice.
--
-- When the form is a single variable u -- the case where elimination
-- solves y_j = x_w, which is what it does whenever the pivot's wire
-- holds y_j alone -- the result has a closed form:
--
--   P[v ← u] = (P ∖ᵛ v) + u · (P /ᵛ v),
--
-- where u · R has, at γ ∋ u, the coefficient R γ + R (γ ∖ u) (the
-- terms u·δ of the product with δ = γ and δ = γ ∖ u), and 0 elsewhere
-- (_·ᵛ_).  substVar is that polynomial; reading one of its
-- coefficients reads at most three of P.  subst-var proves the two
-- equal coefficient by coefficient, for every P, v and u, through
-- their values: eval-subst gives the value of the substitution,
-- eval-·ᵛ that of the product, and PathSum.Polynomial.Bind.poly-ext
-- (Möbius inversion) turns equal values into equal coefficients.
-- Finally ∖ʸ-≗: dropping a path variable (PathSum.Reorder._∖ʸ_)
-- respects pointwise equality, as it only renumbers.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Polynomial.SubstVar where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Bool.Properties using (∨-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using
  (Subset; inside; outside; ⁅_⁆; ⊥; _∪_; _∈_)
  renaming (_-_ to _∖_)
open import Data.Fin.Subset.Properties using (∪-identityʳ; p─⊥≡p)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; _+_; _*_)
open import Data.Integer.Properties using
  (+-comm; +-identityˡ; *-identityˡ; *-zeroˡ)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using (_∷_; here; there; insertAt)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using
  (Dec; yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Linear using (varᴸ; eval-liftᴸ; valᴸ-var)
open import PathSum.Polynomial using
  (Poly; Mon; Var; x[_]; y[_]; ⟪_⟫; _∈ᵐ_; _∈ᵐ?_; _∪ᵐ_; _∖ᵐ_; 0ᴾ; _+ᴾ_;
   eval; subst)
open import PathSum.Polynomial.Bind using (poly-ext)
open import PathSum.Polynomial.Product using (eval-0ᴾ)
open import PathSum.Polynomial.Properties using
  (_∖ᵛ_; _/ᵛ_; valᵛ; eval-split; eval-subst; eval-ext; eval-+ᴾ;
   v∈δ∪⟪v⟫)
open import PathSum.Reorder using (_∖ʸ_)

private
  variable
    k n m : ℕ


------------------------------------------------------------------------
-- A monomial with a variable added and removed again

private
  -- (p ∪ {i}) ∖ i is p, when i is not in p.

  ∪⁅⁆∖ : (p : Subset k) (i : Fin k) → ¬ (i ∈ p) → (p ∪ ⁅ i ⁆) ∖ i ≡ p
  ∪⁅⁆∖ (outside ∷ p) zero    i∉p =
    cong (outside ∷_) (trans (p─⊥≡p (p ∪ ⊥)) (∪-identityʳ p))
  ∪⁅⁆∖ (inside  ∷ p) zero    i∉p = contradiction here i∉p
  ∪⁅⁆∖ (b ∷ p)       (suc i) i∉p =
    cong₂ _∷_ (∨-identityʳ b) (∪⁅⁆∖ p i (i∉p ∘ there))

∪⟪⟫∖ : (δ : Mon n m) (u : Var n m) → ¬ (u ∈ᵐ δ) → (δ ∪ᵐ ⟪ u ⟫) ∖ᵐ u ≡ δ
∪⟪⟫∖ (α , β) x[ i ] u∉δ = cong₂ _,_ (∪⁅⁆∖ α i u∉δ) (∪-identityʳ β)
∪⟪⟫∖ (α , β) y[ j ] u∉δ = cong₂ _,_ (∪-identityʳ α) (∪⁅⁆∖ β j u∉δ)


------------------------------------------------------------------------
-- Multiplying by a variable

-- u · R: at a monomial containing u, the terms of R there and at the
-- monomial without u; elsewhere nothing.

infixr 7 _·ᵛ_

_·ᵛ_ : Var n m → Poly n m → Poly n m
(u ·ᵛ R) γ = if ⌊ u ∈ᵐ? γ ⌋ then R γ + R (γ ∖ᵐ u) else 0ℤ

-- Its value is the value of u times that of R.  Split at u: the part
-- free of u vanishes, and the quotient by u is R's quotient plus R's
-- part free of u, whose values add up to R's where u is 1.

private
  bit : Bool → ℤ
  bit b = if b then 1ℤ else 0ℤ

  ⌊⌋-true : {A : Set} (d : Dec A) → A → ⌊ d ⌋ ≡ true
  ⌊⌋-true (yes _)  _ = refl
  ⌊⌋-true (no ¬a) a = contradiction a ¬a

  free-part : ∀ (b : Bool) (t : ℤ) →
              (if b then 0ℤ else (if b then t else 0ℤ)) ≡ 0ℤ
  free-part true  t = refl
  free-part false t = refl

  ·ᵛ∖ : (u : Var n m) (R : Poly n m) → ∀ γ → ((u ·ᵛ R) ∖ᵛ u) γ ≡ 0ᴾ γ
  ·ᵛ∖ u R γ = free-part ⌊ u ∈ᵐ? γ ⌋ (R γ + R (γ ∖ᵐ u))

  ·ᵛ/ : (u : Var n m) (R : Poly n m) →
        ∀ δ → ((u ·ᵛ R) /ᵛ u) δ ≡ ((R /ᵛ u) +ᴾ (R ∖ᵛ u)) δ
  ·ᵛ/ u R δ = by (u ∈ᵐ? δ)
    where
    by : (d : Dec (u ∈ᵐ δ)) →
         (if ⌊ d ⌋ then 0ℤ else (u ·ᵛ R) (δ ∪ᵐ ⟪ u ⟫)) ≡
         (if ⌊ d ⌋ then 0ℤ else R (δ ∪ᵐ ⟪ u ⟫)) +
         (if ⌊ d ⌋ then 0ℤ else R δ)
    by (yes _)   = refl
    by (no u∉δ) = trans
      (cong (λ b → if b then R (δ ∪ᵐ ⟪ u ⟫) + R ((δ ∪ᵐ ⟪ u ⟫) ∖ᵐ u)
                   else 0ℤ)
            (⌊⌋-true (u ∈ᵐ? (δ ∪ᵐ ⟪ u ⟫)) (v∈δ∪⟪v⟫ δ u)))
      (cong (λ γ → R (δ ∪ᵐ ⟪ u ⟫) + R γ) (∪⟪⟫∖ δ u u∉δ))

  arith : ∀ (b : Bool) (A B : ℤ) →
          0ℤ + bit b * (A + B) ≡ bit b * (B + bit b * A)
  arith true  A B = trans (+-identityˡ (1ℤ * (A + B)))
    (trans (*-identityˡ (A + B))
      (trans (+-comm A B)
        (sym (trans (*-identityˡ (B + 1ℤ * A))
                    (cong (B +_) (*-identityˡ A))))))
  arith false A B = trans (+-identityˡ (0ℤ * (A + B)))
    (trans (*-zeroˡ (A + B)) (sym (*-zeroˡ (B + 0ℤ * A))))

eval-·ᵛ : (u : Var n m) (R : Poly n m) (x : Fin n → Bool) (y : Fin m → Bool) →
          eval (u ·ᵛ R) x y ≡ (if valᵛ u x y then 1ℤ else 0ℤ) * eval R x y
eval-·ᵛ u R x y = trans (eval-split (u ·ᵛ R) u x y)
  (trans (cong₂ (λ a b → a + bit (valᵛ u x y) * b)
    (trans (eval-ext ((u ·ᵛ R) ∖ᵛ u) 0ᴾ (·ᵛ∖ u R) x y) (eval-0ᴾ x y))
    (trans (eval-ext ((u ·ᵛ R) /ᵛ u) ((R /ᵛ u) +ᴾ (R ∖ᵛ u)) (·ᵛ/ u R) x y)
           (eval-+ᴾ (R /ᵛ u) (R ∖ᵛ u) x y)))
  (trans (arith (valᵛ u x y) (eval (R /ᵛ u) x y) (eval (R ∖ᵛ u) x y))
         (cong (bit (valᵛ u x y) *_) (sym (eval-split R u x y)))))


------------------------------------------------------------------------
-- Substituting a variable for a variable

substVar : Poly n m → Var n m → Var n m → Poly n m
substVar P v u = (P ∖ᵛ v) +ᴾ (u ·ᵛ (P /ᵛ v))

-- The substitution of PathSum.Polynomial at the form u (constant 0,
-- the single variable u) is substVar, coefficient by coefficient.

subst-var : (P : Poly n m) (v u : Var n m) →
            ∀ γ → subst P v false ⟪ u ⟫ γ ≡ substVar P v u γ
subst-var P v u = poly-ext (subst P v false ⟪ u ⟫) (substVar P v u) values
  where
  values : ∀ x y → eval (subst P v false ⟪ u ⟫) x y ≡
                   eval (substVar P v u) x y
  values x y = trans (eval-subst P v false ⟪ u ⟫ x y)
    (trans (cong (λ a → eval (P ∖ᵛ v) x y + a * eval (P /ᵛ v) x y)
                 (trans (eval-liftᴸ (varᴸ u) x y)
                        (cong bit (valᴸ-var u x y))))
    (trans (cong (eval (P ∖ᵛ v) x y +_)
                 (sym (eval-·ᵛ u (P /ᵛ v) x y)))
           (sym (eval-+ᴾ (P ∖ᵛ v) (u ·ᵛ (P /ᵛ v)) x y))))


------------------------------------------------------------------------
-- Dropping a path variable respects pointwise equality

∖ʸ-≗ : (j : Fin (suc m)) {P Q : Poly n (suc m)} → (∀ γ → P γ ≡ Q γ) →
       ∀ γ → (P ∖ʸ j) γ ≡ (Q ∖ʸ j) γ
∖ʸ-≗ j h (α , s) = h (α , insertAt s j outside)
