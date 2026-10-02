------------------------------------------------------------------------
-- Presentations of groups
--
-- At order 2 the linear rules are all of figure 2
--
-- Figure 2 of Amy's paper (QPL 2018) has four rules: [Elim], [ω] and
-- [HH] with any Boolean-valued quotient, and [Case].  PathSum.Anywhere
-- formalises the first three with Z₂-linear quotients only (_⟶ᵍ_), and
-- that is the calculus the polynomial-time normaliser rewrites with
-- (PathSum.Cost.Normalise); PathSum.Full has all four, at any
-- variables and pairs (_⟶ᶠ_).  In general the two have different normal
-- forms: a step of figure 2 with a quotient that is not linear can
-- apply where no linear step does (PathSum.Full.Order2.Sharp, at order
-- 3).  This module proves that at order 2 they have the same: whenever
-- a step of _⟶ᶠ_ applies to a path-sum whose phase has order at most
-- 2, so does a step of _⟶ᵍ_ (⟶ᶠ⇒⟶ᵍ), so a path-sum of order at most 2
-- is irreducible under all of figure 2 exactly when it is irreducible
-- under the linear rules (Irreducible⇔Irreducibleᶠ).  Nothing is
-- assumed about the outputs: in particular the path variables need not
-- be internal.  The precision is M = 3 + M₀, as in
-- PathSum.Full.Clifford.
--
-- The argument is about two coefficients (all coefficients are read
-- modulo 1).  At order 2 the quotient H of the phase by a path
-- variable has a multiple of ¼ as its constant coefficient, multiples
-- of ½ as its linear ones and nothing else, so it is ¼a + ½ times a
-- linear form whose variables are those with an odd ½-coefficient in H
-- (PathSum.Clifford.decompose).  So a linear [ω] applies as soon as
-- H's constant coefficient is ¼ modulo ½ (ω-cert), and a linear [HH]
-- as soon as it is 0 modulo ½ and some path variable y_i has an odd
-- ½-coefficient in H (hh-cert); [Elim] has the same premise in both
-- calculi.  A general step supplies those two coefficients:
--
-- * [ω] with any quotient Q: H ≈ ¼ + ½Q, so H's constant coefficient
--   is ¼ modulo ½.
-- * [HH] with any quotient: H ≈ ½(y_i + Q) with Q free of y_i, so the
--   constant coefficient is a multiple of ½ and y_i's is ½.
-- * [Case] at (y₀ , y₁): the y₀y₁ coefficient of the phase is ½, the
--   y₀ coefficient is ¼X(1) + ½Q(1) and the y₁ coefficient is
--   ¼(1 - X(1)) + ½Q′(1).  If the constant coefficient X(1) of X is
--   even, the quotient by y₀ has constant coefficient 0 modulo ½ and
--   y₁-coefficient ½: [HH] at y₀ substituting for y₁.  If it is odd,
--   the same holds with y₀ and y₁ exchanged: [HH] at y₁.  (At order 2
--   X is in fact the constant X(1) -- PathSum.Full.Clifford shows as
--   much, privately, for its Clifford path-sums -- but only the parity
--   of X(1) is used here, and none of the Boolean-valuedness
--   conditions.)
--
-- None of this is about one variable rather than another, but the
-- steps of _⟶ᶠ_ come with renumberings: a head rule after front j, or
-- after the double renumbering front l′ ∘ front j (the derivation
-- at j ∘ at l′), and the linear step built above is a step on the
-- renumbered path-sum.  Carrying it back is front-step: a linear step
-- on front j ξ is one on ξ.  A step at the head of front j ξ is the
-- step at y_j; one at the head of front zero (front j ξ) is too, front
-- zero moving nothing; and one at the head of front (suc l) (front j ξ)
-- removes the original variable v = punchIn j l, so it is matched by a
-- step at v, whose quotient is the same polynomial with the remaining
-- variables renumbered (PathSum.Reorder.Commute, the missing lemma of
-- the WP-POLYTIME report: a Vec.insertAt commutation).  [Elim]'s
-- premise transports coefficient by coefficient, the substituted
-- variable of [HH] moves with the renumbering, and the two coefficients
-- [ω] and [HH] are read from are the constant one and a single path
-- variable's, which the renumbering keeps.  The linear step on ξ need
-- not have the same reduct as the general one -- it may keep its other
-- variables in another order, or substitute a different variable, or
-- be an [HH] where the general step was a [Case] -- since only its
-- existence is claimed.
--
-- With PathSum.Cost.Irreducible this makes the normal forms of the
-- polynomial-time normaliser normal forms of all of figure 2 at order
-- 2.  At order 2, Irreducibleᶠ is also decided by the linear search of
-- PathSum.Anywhere.Match (irreducibleᶠ?ᴸ) rather than by
-- PathSum.Full.Match's search over every pair (neither search is
-- costed here, and both are exponential).  For a
-- Clifford circuit C every reduct of ⟦ C ⟧ᴿ by figure 2 has order 2
-- (PathSum.Full.Clifford), so along any such reduction the two notions
-- agree (circuit-irreducible⇔), and corollary 4.4 for every normal form
-- (PathSum.Full.Clifford.corollary-4-4-normalᶠ) needs only that no
-- linear rule applies at the end (corollary-4-4-normalᴸ).
--
-- The bound 2 cannot be raised to 3: PathSum.Full.Order2.Sharp exhibits
-- a path-sum of order 3, with internal path variables, to which no
-- linear rule applies but figure 2's [HH] with a non-linear quotient
-- does.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Full.Order2 (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using (Fin; zero; suc; punchIn)
open import Data.Fin.Subset using (_∈_)
open import Data.Fin.Subset.Properties using (⊥⊆; x∈⁅x⁆; x∈⁅y⁆⇒x≡y)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; ∣-refl; ∣-trans; ∣⇒∣ᵤ; ∣m∣n⇒∣m+n; ∣m∣n⇒∣m-n; ∣m⇒∣-m; ∣m⇒∣m*n;
   *-cancelˡ-∣)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; *-identityˡ; *-identityʳ; *-zeroʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc; _∸_)
open import Data.Nat.Divisibility using (∣1⇒≡1)
open import Data.Nat.Properties using (m^n≢0)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no; map′)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using (PathSum; phase; out; head-part; idPS)
open import PathSum.Circuit M using (Circuit; ⟦_⟧; ⟦_⟧ᴿ)
open import PathSum.Order M using (Ord≤; pow; pow-suc; parity)
open import PathSum.Polynomial using
  (Mon; Poly; Var; x[_]; y[_]; 1ᵐ; ⟪_⟫; _∈ᵐ_; _∈ᵐ?_; _⊆ᵐ_; _⊆ᵐ?_; _≟ᵐ_;
   ∥_∥; 0ᴾ; κ; μ; sgn; negpow; liftXor; _+ᴾ_; _-ᴾ_; _·ᴾ_; _≈[_]_; NoVar)
open import PathSum.Polynomial.Properties using
  (liftXor-0; ∥⟪v⟫∥≡1; ∥1ᵐ∥≡0)
open import PathSum.Polynomial.Substitution using (Absent; q₁₁; q₁₀; q₀₁)
open import PathSum.Reduction M using (_⟶_; elim; ω; hh; ¼; ½)
open import PathSum.Reduction.General M using
  (_⟶ᴳ_; elimᴳ; ωᴳ; hhᴳ; caseᴳ)
open import PathSum.Reorder using (front; frontᴾ; _/ʸ_; NoVar-front)
open import PathSum.Reorder.Commute using
  (swapIdx; moved; /ʸ-1ᵐ; /ʸ-⟪⟫; ≈0-front-front; NoVar-front-front;
   NoVar-unfront-zero)
open import PathSum.Anywhere M using (_⟶ᵍ_; plain; at; Ord≤-front)
open import PathSum.Anywhere.Match M using
  (Internal₀; HeadStep; Irreducible; irreducible?)
open import PathSum.Full M using (_⟶ᶠ_; _⟶ᶠ*_)
open import PathSum.Full.Clifford M₀ using
  (⟶ᶠ*-Clifford; circuit-Clifford; corollary-4-4-normalᶠ)
open import PathSum.Full.Canonical M using (½∣pow)
open import PathSum.Full.Match M using
  (Irreducibleᶠ; Irreducibleᶠ⇒Irreducible)

import PathSum.Clifford
import PathSum.Denotation

private
  module Den = PathSum.Denotation M₀
  module Cliff = PathSum.Clifford M₀ Den.semantics

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- Some linear rule applies

-- A step of _⟶ᵍ_ out of ξ: [Elim], [ω] or [HH] with a linear quotient,
-- at some path variable.

LinStep : PathSum n k m → Set
LinStep {n} ξ = ∃ λ k′ → ∃ λ m′ → ∃ λ (ζ : PathSum n k′ m′) → ξ ⟶ᵍ ζ

private
  -- A head step is a step.
  lift : {ξ : PathSum n k m} → HeadStep ξ → LinStep ξ
  lift (_ , _ , _ , s) = _ , _ , _ , plain s


------------------------------------------------------------------------
-- Arithmetic

private
  2∤1 : ¬ ((+ 2) ∣ 1ℤ)
  2∤1 h with ∣1⇒≡1 (∣⇒∣ᵤ h)
  ... | ()

  2∤sgn : (c : Bool) → ¬ ((+ 2) ∣ sgn c)
  2∤sgn false = 2∤1
  2∤sgn true  = λ h → 2∤1 (∣m⇒∣-m h)

  -- 2^M = ½ · 2.
  half-cancel : ∀ {a} → pow M ∣ (½ * a) → (+ 2) ∣ a
  half-cancel {a} h = *-cancelˡ-∣ ½ {{m^n≢0 2 (M ∸ 1)}}
    (subst (_∣ (½ * a)) (pow-suc (M ∸ 1)) h)

  -- ½ = ¼ · 2.
  ½≡ : ½ ≡ ¼ * (+ 2)
  ½≡ = pow-suc (M ∸ 2)

  -- A number congruent to ½u modulo 2^M is a multiple of ½ ...
  half-div : ∀ {a} u → pow M ∣ (a - ½ * u) → ½ ∣ a
  half-div {a} u h = subst (½ ∣_) (shape a (½ * u))
    (∣m∣n⇒∣m+n (∣-trans ½∣pow h) (∣m⇒∣m*n u ∣-refl))
    where
    shape : ∀ a x → (a - x) + x ≡ a
    shape = solve 2 (λ a x → (a :- x) :+ x := a) refl

  -- ... and, for u odd, not a multiple of 2^M.
  odd-half : ∀ {a} u → pow M ∣ (a - ½ * u) → ¬ ((+ 2) ∣ u) →
             ¬ (pow M ∣ a)
  odd-half {a} u h ¬2∣u d = ¬2∣u (half-cancel
    (subst (pow M ∣_) (shape a (½ * u)) (∣m∣n⇒∣m-n d h)))
    where
    shape : ∀ a x → a - (a - x) ≡ x
    shape = solve 2 (λ a x → a :- (a :- x) := x) refl

  -- A number congruent to b + ½u modulo 2^M is b modulo ½.
  shift-div : ∀ a b u → pow M ∣ (a - (b + ½ * u)) → ½ ∣ (a - b)
  shift-div a b u h = subst (½ ∣_) (shape a b (½ * u))
    (∣m∣n⇒∣m+n (∣-trans ½∣pow h) (∣m⇒∣m*n u ∣-refl))
    where
    shape : ∀ a b x → (a - (b + x)) + x ≡ a - b
    shape = solve 3 (λ a b x → (a :- (b :+ x)) :+ x := a :- b) refl


------------------------------------------------------------------------
-- Coefficients of constants, monic variables and linear liftings

private
  κ-1ᵐ : (c : ℤ) → κ {n} {m} c 1ᵐ ≡ c
  κ-1ᵐ {n} {m} c with (1ᵐ {n} {m}) ≟ᵐ 1ᵐ
  ... | yes _ = refl
  ... | no ¬p = contradiction refl ¬p

  κ-0 : (γ : Mon n m) → κ {n} {m} 0ℤ γ ≡ 0ℤ
  κ-0 γ with γ ≟ᵐ 1ᵐ
  ... | yes _ = refl
  ... | no  _ = refl

  μ-⟪⟫ : (v : Var n m) → μ v ⟪ v ⟫ ≡ 1ℤ
  μ-⟪⟫ v with ⟪ v ⟫ ≟ᵐ ⟪ v ⟫
  ... | yes _ = refl
  ... | no ¬p = contradiction refl ¬p

  ⟪v⟫≢1ᵐ : (v : Var n m) → ⟪ v ⟫ ≢ 1ᵐ
  ⟪v⟫≢1ᵐ {n} {m} v ⟪v⟫≡1ᵐ
    with trans (sym (∥⟪v⟫∥≡1 v)) (trans (cong ∥_∥ ⟪v⟫≡1ᵐ) (∥1ᵐ∥≡0 {n} {m}))
  ... | ()

  ⟪y⟫⊆ : (i : Fin m) (S : Mon n m) → y[ i ] ∈ᵐ S → ⟪ y[ i ] ⟫ ⊆ᵐ S
  ⟪y⟫⊆ i (α , β) i∈β =
    ⊥⊆ , (λ x∈⁅i⁆ → subst (_∈ β) (sym (x∈⁅y⁆⇒x≡y i x∈⁅i⁆)) i∈β)

  liftXor-∈ : (c : Bool) (S : Mon n m) {γ : Mon n m} → γ ≢ 1ᵐ → γ ⊆ᵐ S →
              liftXor c S γ ≡ sgn c * negpow (∥ γ ∥ ∸ 1)
  liftXor-∈ c S {γ} γ≢ γ⊆ with γ ≟ᵐ 1ᵐ
  ... | yes p = contradiction p γ≢
  ... | no  _ with γ ⊆ᵐ? S
  ...   | yes _ = refl
  ...   | no ¬q = contradiction γ⊆ ¬q

  -- The coefficient of a path variable of S in the lifting of c ⊕ ⨁S
  -- is ±1.
  liftXor-⟪⟫ : (c : Bool) (S : Mon n m) (i : Fin m) → y[ i ] ∈ᵐ S →
               liftXor c S ⟪ y[ i ] ⟫ ≡ sgn c
  liftXor-⟪⟫ {n} c S i i∈S = trans
    (liftXor-∈ c S (⟪v⟫≢1ᵐ y[ i ]) (⟪y⟫⊆ i S i∈S))
    (trans (cong (λ z → sgn c * negpow (z ∸ 1)) (∥⟪v⟫∥≡1 {n} y[ i ]))
      (trans (cong (sgn c *_) (*-identityˡ 1ℤ)) (*-identityʳ (sgn c))))


------------------------------------------------------------------------
-- Linear steps from two coefficients

-- At order 2 the quotient H of the phase by y₀ is ¼a + ½(c ⊕ ⨁S) with
-- S the support of H (PathSum.Clifford.decompose); a is read off H's
-- constant coefficient modulo ½.  So [ω] applies when that coefficient
-- is ¼ modulo ½ ...

ω-cert : (χ : PathSum n (suc k) (suc m)) → Ord≤ 2 (phase χ) →
         ½ ∣ (head-part (phase χ) 1ᵐ - ¼) → Internal₀ χ → HeadStep χ
ω-cert χ ord c₀ o =
  _ , _ , _ , ω χ (proj₁ dec) (Cliff.supp H) (proj₂ dec) o
  where
  H = head-part (phase χ)

  dec = Cliff.decompose H ¼ (Cliff.prof⟪⟫ ord) (Cliff.prof≥2 ord) c₀

-- ... and [HH] when it is 0 modulo ½ and some path variable has an
-- odd ½-coefficient: that variable is in the support.

hh-cert : (χ : PathSum n k (suc m)) → Ord≤ 2 (phase χ) →
          ½ ∣ head-part (phase χ) 1ᵐ → (i : Fin m) →
          ¬ (pow M ∣ head-part (phase χ) ⟪ y[ i ] ⟫) →
          Internal₀ χ → HeadStep χ
hh-cert χ ord c₀ i ¬d o = _ , _ , _ , hh χ i c S (i∈S (y[ i ] ∈ᵐ? S)) eq′ o
  where
  H = head-part (phase χ)
  S = Cliff.supp H

  dec = Cliff.decompose H 0ℤ (Cliff.prof⟪⟫ ord) (Cliff.prof≥2 ord)
    (subst (pow (M ∸ 1) ∣_) (sym (+-identityʳ (H 1ᵐ))) c₀)

  c : Bool
  c = proj₁ dec

  eq′ : H ≈[ pow M ] (½ ·ᴾ liftXor c S)
  eq′ γ = subst (λ z → pow M ∣ (H γ - z))
    (trans (cong (_+ (½ * liftXor c S γ)) (κ-0 γ)) (+-identityˡ _))
    (proj₂ dec γ)

  i∈S : Dec (y[ i ] ∈ᵐ S) → y[ i ] ∈ᵐ S
  i∈S (yes p) = p
  i∈S (no ¬p) = contradiction
    (subst (pow M ∣_)
      (trans (cong (λ z → H ⟪ y[ i ] ⟫ - ½ * z)
               (liftXor-0 c S ⟪ y[ i ] ⟫ y[ i ] (x∈⁅x⁆ i) ¬p))
        (trans (cong (H ⟪ y[ i ] ⟫ -_) (*-zeroʳ ½))
               (+-identityʳ (H ⟪ y[ i ] ⟫))))
      (eq′ ⟪ y[ i ] ⟫))
    ¬d


------------------------------------------------------------------------
-- A general head step gives a linear step

-- [Elim] is the same rule in both calculi; [ω] and [HH] give the two
-- coefficients; [Case] gives an [HH] at y₀ or at y₁, as the constant
-- coefficient of X is even or odd.

private
  case-step : (χ : PathSum n (suc (suc k)) (suc (suc m)))
              (X Q Q′ : Poly n m) → Ord≤ 2 (phase χ) →
              q₁₁ (phase χ) ≈[ pow M ] κ ½ →
              q₁₀ (phase χ) ≈[ pow M ] ((¼ ·ᴾ X) +ᴾ (½ ·ᴾ Q)) →
              q₀₁ (phase χ) ≈[ pow M ]
                ((¼ ·ᴾ (κ 1ℤ -ᴾ X)) +ᴾ (½ ·ᴾ Q′)) →
              Internal₀ χ →
              (∀ w → NoVar (+ 2) y[ suc zero ] (out χ w)) →
              LinStep χ
  case-step {n} {m = m} χ X Q Q′ ord e₁₁ e₁₀ e₀₁ o₀ o₁ =
    by (parity (X 1ᵐ))
    where
    P = phase χ

    -- The y₀y₁ coefficient is ½, which 2^M does not divide.
    ¬d₁₁ : ¬ (pow M ∣ q₁₁ P 1ᵐ)
    ¬d₁₁ = odd-half 1ℤ
      (subst (λ z → pow M ∣ (q₁₁ P 1ᵐ - z))
             (trans (κ-1ᵐ {n} {m} ½) (sym (*-identityʳ ½))) (e₁₁ 1ᵐ))
      2∤1

    by : (∃ λ r → X 1ᵐ ≡ r * (+ 2)) ⊎ (∃ λ r → X 1ᵐ ≡ (r * (+ 2)) + 1ℤ) →
         LinStep χ
    -- X 1ᵐ even: [HH] at y₀, substituting for y₁.
    by (inj₁ (r , X≡)) =
      lift (hh-cert χ ord (half-div (r + Q 1ᵐ) h₀) zero ¬d₁₁ o₀)
      where
      shape : ∀ f r q → (f * (r * (+ 2))) + ((f * (+ 2)) * q) ≡
                        (f * (+ 2)) * (r + q)
      shape = solve 3 (λ f r q →
        (f :* (r :* con (+ 2))) :+ ((f :* con (+ 2)) :* q) :=
        (f :* con (+ 2)) :* (r :+ q)) refl

      h₀ : pow M ∣ (q₁₀ P 1ᵐ - ½ * (r + Q 1ᵐ))
      h₀ = subst (λ z → pow M ∣ (q₁₀ P 1ᵐ - z))
        (trans (cong (λ x → ¼ * x + ½ * Q 1ᵐ) X≡)
          (trans (cong (λ h → ¼ * (r * (+ 2)) + h * Q 1ᵐ) ½≡)
            (trans (shape ¼ r (Q 1ᵐ))
                   (cong (_* (r + Q 1ᵐ)) (sym ½≡)))))
        (e₁₀ 1ᵐ)
    -- X 1ᵐ odd: [HH] at y₁, substituting for y₀.
    by (inj₂ (r , X≡)) = _ , _ , _ , at (suc zero) (proj₂ (proj₂ (proj₂
      (hh-cert (front (suc zero) χ) (Ord≤-front (suc zero) ord)
         (half-div (Q′ 1ᵐ - r) h₁) zero ¬d₁₁
         (λ w → NoVar-front (suc zero) (out χ w) (o₁ w))))))
      where
      shape : ∀ f r q → (f * (1ℤ - ((r * (+ 2)) + 1ℤ))) + ((f * (+ 2)) * q) ≡
                        (f * (+ 2)) * (q - r)
      shape = solve 3 (λ f r q →
        (f :* (con 1ℤ :- ((r :* con (+ 2)) :+ con 1ℤ))) :+
          ((f :* con (+ 2)) :* q) :=
        (f :* con (+ 2)) :* (q :- r)) refl

      h₁ : pow M ∣ (q₀₁ P 1ᵐ - ½ * (Q′ 1ᵐ - r))
      h₁ = subst (λ z → pow M ∣ (q₀₁ P 1ᵐ - z))
        (trans (cong₂ (λ u x → ¼ * (u - x) + ½ * Q′ 1ᵐ)
                      (κ-1ᵐ {n} {m} 1ℤ) X≡)
          (trans (cong (λ h → ¼ * (1ℤ - ((r * (+ 2)) + 1ℤ)) + h * Q′ 1ᵐ)
                       ½≡)
            (trans (shape ¼ r (Q′ 1ᵐ))
                   (cong (_* (Q′ 1ᵐ - r)) (sym ½≡)))))
        (e₀₁ 1ᵐ)

linear-head : {χ : PathSum n k m} {ζ : PathSum n k′ m′} →
              Ord≤ 2 (phase χ) → χ ⟶ᴳ ζ → LinStep χ
linear-head ord (elimᴳ χ eq o) = _ , _ , _ , plain (elim χ eq o)
linear-head {n} {m = suc m} ord (ωᴳ χ Q bQ eq o) =
  lift (ω-cert χ ord
    (shift-div (head-part (phase χ) 1ᵐ) ¼ (Q 1ᵐ)
      (subst (λ z → pow M ∣ (head-part (phase χ) 1ᵐ - (z + ½ * Q 1ᵐ)))
             (κ-1ᵐ {n} {m} ¼) (eq 1ᵐ)))
    o)
linear-head {n} ord (hhᴳ χ i Q bQ absQ eq o) =
  lift (hh-cert χ ord (half-div (μ {n} y[ i ] 1ᵐ + Q 1ᵐ) (eq 1ᵐ)) i
    (odd-half (μ {n} y[ i ] ⟪ y[ i ] ⟫ + Q ⟪ y[ i ] ⟫) (eq ⟪ y[ i ] ⟫)
      (subst (λ u → ¬ ((+ 2) ∣ u))
        (sym (cong₂ _+_ (μ-⟪⟫ {n} y[ i ]) (absQ ⟪ y[ i ] ⟫ (x∈⁅x⁆ i))))
        2∤1))
    o)
linear-head ord (caseᴳ χ X Q Q′ bX bQ bQ′ e₁₁ e₁₀ e₀₁ o₀ o₁) =
  case-step χ X Q Q′ ord e₁₁ e₁₀ e₀₁ o₀ o₁


------------------------------------------------------------------------
-- A linear step after a renumbering is a linear step

-- The core: a linear head step on front (suc l) (front j ξ) gives one
-- at y_(punchIn j l), read off the coefficients that
-- PathSum.Reorder.Commute relates.

pivot : (ξ : PathSum n k (suc (suc m))) → Ord≤ 2 (phase ξ) →
        (j : Fin (suc (suc m))) (l : Fin (suc m)) {ζ : PathSum n k′ m′} →
        front (suc l) (front j ξ) ⟶ ζ → HeadStep (front (punchIn j l) ξ)
pivot ξ ord j l (elim _ eq o) =
  _ , _ , _ ,
  elim (front (punchIn j l) ξ) (≈0-front-front (pow M) j l (phase ξ) eq)
       (λ w → NoVar-front-front j l (out ξ w) (o w))
pivot {n} {m = m} ξ ord j l (ω _ c S eq o) =
  ω-cert (front (punchIn j l) ξ) (Ord≤-front (punchIn j l) ord)
    (subst (λ z → ½ ∣ (z - ¼)) (/ʸ-1ᵐ j l (phase ξ))
      (shift-div (head-part (frontᴾ (suc l) (frontᴾ j (phase ξ))) 1ᵐ) ¼
                 (liftXor c S 1ᵐ)
        (subst (λ z → pow M ∣
                  (head-part (frontᴾ (suc l) (frontᴾ j (phase ξ))) 1ᵐ -
                   (z + ½ * liftXor c S 1ᵐ)))
               (κ-1ᵐ {n} {suc m} ¼) (eq 1ᵐ))))
    (λ w → NoVar-front-front j l (out ξ w) (o w))
pivot ξ ord j l (hh _ i c S i∈S eq o) =
  hh-cert (front (punchIn j l) ξ) (Ord≤-front (punchIn j l) ord)
    (subst (½ ∣_) (/ʸ-1ᵐ j l (phase ξ))
      (half-div (liftXor c S 1ᵐ) (eq 1ᵐ)))
    (moved (swapIdx j l) i)
    (subst (λ z → ¬ (pow M ∣ z)) (/ʸ-⟪⟫ j l (phase ξ) i)
      (odd-half (liftXor c S ⟪ y[ i ] ⟫) (eq ⟪ y[ i ] ⟫)
        (subst (λ u → ¬ ((+ 2) ∣ u)) (sym (liftXor-⟪⟫ c S i i∈S))
               (2∤sgn c))))
    (λ w → NoVar-front-front j l (out ξ w) (o w))

private
  -- front zero moves nothing.
  unzero : {χ : PathSum n k (suc m)} {ζ : PathSum n k′ m′} →
           front zero χ ⟶ ζ → HeadStep χ
  unzero {χ = χ} (elim _ eq o) =
    _ , _ , _ , elim χ eq (λ w → NoVar-unfront-zero (out χ w) (o w))
  unzero {χ = χ} (ω _ c S eq o) =
    _ , _ , _ , ω χ c S eq (λ w → NoVar-unfront-zero (out χ w) (o w))
  unzero {χ = χ} (hh _ i c S i∈S eq o) =
    _ , _ , _ ,
    hh χ i c S i∈S eq (λ w → NoVar-unfront-zero (out χ w) (o w))

-- A linear step on front j ξ is one on ξ: at y_j, at y_j again, or at
-- y_(punchIn j l), as it was taken at the head of front j ξ, of
-- front zero (front j ξ) or of front (suc l) (front j ξ).

front-step : (ξ : PathSum n k (suc m)) → Ord≤ 2 (phase ξ) →
             (j : Fin (suc m)) → LinStep (front j ξ) → LinStep ξ
front-step ξ ord j (_ , _ , _ , plain s)    = _ , _ , _ , at j s
front-step ξ ord j (_ , _ , _ , at zero s)  =
  _ , _ , _ , at j (proj₂ (proj₂ (proj₂ (unzero {χ = front j ξ} s))))
front-step {m = zero}  ξ ord j (_ , _ , _ , at (suc ()) s)
front-step {m = suc m} ξ ord j (_ , _ , _ , at (suc l) s) =
  _ , _ , _ , at (punchIn j l) (proj₂ (proj₂ (proj₂ (pivot ξ ord j l s))))


------------------------------------------------------------------------
-- Every step of figure 2 gives a linear step

-- At order 2: the head step of a derivation of _⟶ᶠ_ gives a linear
-- step on the path-sum it acts on (linear-head), and front-step carries
-- it back through each renumbering of the derivation.

⟶ᶠ⇒⟶ᵍ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
        Ord≤ 2 (phase ξ) → ξ ⟶ᶠ ζ → LinStep ξ
⟶ᶠ⇒⟶ᵍ           ord (plain (plain s)) = linear-head ord s
⟶ᶠ⇒⟶ᵍ {ξ = ξ} ord (plain (at j s))  =
  front-step ξ ord j (linear-head (Ord≤-front j ord) s)
⟶ᶠ⇒⟶ᵍ {ξ = ξ} ord (at j (plain s))  =
  front-step ξ ord j (linear-head (Ord≤-front j ord) s)
⟶ᶠ⇒⟶ᵍ {ξ = ξ} ord (at j (at j′ s)) =
  front-step ξ ord j
    (front-step (front j ξ) (Ord≤-front j ord) j′
      (linear-head (Ord≤-front j′ (Ord≤-front j ord)) s))


------------------------------------------------------------------------
-- The two notions of irreducibility agree at order 2

-- Linear irreducibility survives renumbering ...

Irreducible-front : (ξ : PathSum n k (suc m)) → Ord≤ 2 (phase ξ) →
                    Irreducible ξ → (j : Fin (suc m)) →
                    Irreducible (front j ξ)
Irreducible-front ξ ord irr j s =
  irr (proj₂ (proj₂ (proj₂ (front-step ξ ord j (_ , _ , _ , s)))))

-- ... and implies irreducibility under all of figure 2.

Irreducible⇒Irreducibleᶠ : (ξ : PathSum n k m) → Ord≤ 2 (phase ξ) →
                           Irreducible ξ → Irreducibleᶠ ξ
Irreducible⇒Irreducibleᶠ ξ ord irr s =
  irr (proj₂ (proj₂ (proj₂ (⟶ᶠ⇒⟶ᵍ ord s))))

Irreducible⇔Irreducibleᶠ : (ξ : PathSum n k m) → Ord≤ 2 (phase ξ) →
                           Irreducible ξ ⇔ Irreducibleᶠ ξ
Irreducible⇔Irreducibleᶠ ξ ord =
  mk⇔ (Irreducible⇒Irreducibleᶠ ξ ord) Irreducibleᶠ⇒Irreducible

-- So at order 2 irreducibility under all of figure 2 is decided by the
-- linear search.

irreducibleᶠ?ᴸ : (ξ : PathSum n k m) → Ord≤ 2 (phase ξ) →
                 Dec (Irreducibleᶠ ξ)
irreducibleᶠ?ᴸ ξ ord =
  map′ (Irreducible⇒Irreducibleᶠ ξ ord) Irreducibleᶠ⇒Irreducible
       (irreducible? ξ)


------------------------------------------------------------------------
-- Clifford circuits

-- Every step of figure 2 keeps ⟦ C ⟧ᴿ Clifford
-- (PathSum.Full.Clifford), so along any reduction of it the two
-- notions of irreducibility agree ...

circuit-irreducible⇔ : (C : Circuit n) {ξ′ : PathSum n k′ m′} →
                       ⟦ C ⟧ᴿ ⟶ᶠ* ξ′ → Irreducible ξ′ ⇔ Irreducibleᶠ ξ′
circuit-irreducible⇔ C {ξ′} steps = Irreducible⇔Irreducibleᶠ ξ′
  (proj₂ (⟶ᶠ*-Clifford steps (circuit-Clifford C)))

-- ... and corollary 4.4 holds at every end of such a reduction to
-- which no linear rule applies: the circuit is the identity iff no
-- path variable is left and what is left is syntactically |x⟩ ↦ |x⟩.

corollary-4-4-normalᴸ : (C : Circuit n) {ξ′ : PathSum n k′ m′} →
  ⟦ C ⟧ᴿ ⟶ᶠ* ξ′ → Irreducible ξ′ →
  (⟦ C ⟧ Den.≋ idPS ⇔
   (m′ ≡ 0 × k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
corollary-4-4-normalᴸ C {ξ′} steps irr =
  corollary-4-4-normalᶠ C {ξ′ = ξ′} steps
    (Equivalence.to (circuit-irreducible⇔ C {ξ′ = ξ′} steps) irr)
