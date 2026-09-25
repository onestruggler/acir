------------------------------------------------------------------------
-- Presentations of groups
--
-- Ancillas prepared in |0⟩
--
-- A path-sum here maps every basis state of its n qubits (PathSum.Base
-- has no constant inputs), but circuits such as the controlled-T of
-- Amy's example 3.4 use an ancilla that starts in |0⟩, and what the
-- paper claims of them concerns only those inputs: the circuit
-- "implements the controlled-T gate, and provably leaves the ancilla
-- clean".  Preparing qubit i in |0⟩ selects the columns of the
-- operator at the inputs x with x_i = 0, so the claim is an
-- equivalence of operators restricted to those columns:
--
--    ξ ≋[ i ]₀ ζ  ⇔  ∀ x z, x_i = 0 → the entries of ξ and ζ from x
--                    to z agree (after normalisation).
--
-- The path-sum of the circuit on such inputs is obtained by setting
-- x_i to 0 in its polynomials, which drops every term containing x_i
-- (set0; the paper computes this path-sum directly, reading the
-- ancilla as the constant 0).  At the inputs with x_i = 0 it has the
-- circuit's amplitudes (amp-set0), so any equivalence proved of it
-- holds of the circuit restricted to those inputs (set0-≋).  "Leaves
-- the ancilla clean" is then a consequence: if ζ's output on qubit i
-- is 0, every amplitude of ξ from an input with x_i = 0 to an output
-- with z_i = 1 vanishes (clean-ancilla).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.Ancilla (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; not)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _+_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣?_)
open import Data.Integer.Properties using (*-zeroˡ; +-identityʳ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)

open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out)
open import PathSum.Polynomial using (Poly; x[_]; eval)
open import PathSum.Polynomial.Properties using (eval-split; _∖ᵛ_; _/ᵛ_)
open import PathSum.Cyclotomic M₀ using
  (Amp; _≐_; 0ᴬ; zpow; Σᴮ-cong; Σᴮ-0; √2·-map; √2·-0ᴬ; scale;
   scale-map; scale-injective)
open import PathSum.Denotation M₀ using
  (Assign; hits; amp; _≋_; outBit; hits-intro; hits-elim)

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- Setting an input to 0

-- Every term containing x_i dropped, in the phase and in the outputs.

set0 : Fin n → PathSum n k m → PathSum n k m
set0 i ξ = ⟨ phase ξ ∖ᵛ x[ i ] , (λ w → out ξ w ∖ᵛ x[ i ]) ⟩

-- Where x_i is already 0, the terms dropped contribute nothing.

eval-set0 : (P : Poly n m) (i : Fin n) (x : Assign n) (y : Assign m) →
            x i ≡ false → eval (P ∖ᵛ x[ i ]) x y ≡ eval P x y
eval-set0 P i x y x₀ = sym (trans (eval-split P x[ i ] x y)
  (trans (cong (λ b → eval (P ∖ᵛ x[ i ]) x y +
                      ((if b then 1ℤ else 0ℤ) * eval (P /ᵛ x[ i ]) x y))
               x₀)
         (trans (cong (λ u → eval (P ∖ᵛ x[ i ]) x y + u)
                      (*-zeroˡ (eval (P /ᵛ x[ i ]) x y)))
                (+-identityʳ (eval (P ∖ᵛ x[ i ]) x y)))))

-- So there the same paths hit the same outputs, with the same phases.

hits-set0 : (ξ : PathSum n k m) (i : Fin n) (x : Assign n) (y : Assign m)
            (z : Assign n) → x i ≡ false →
            hits (set0 i ξ) x y z ≡ hits ξ x y z
hits-set0 ξ i x y z x₀ = go (hits ξ x y z) refl
  where
  same : ∀ w → outBit (set0 i ξ) x y w ≡ outBit ξ x y w
  same w = cong (λ e → not ⌊ (+ 2) ∣? e ⌋) (eval-set0 (out ξ w) i x y x₀)

  back : hits (set0 i ξ) x y z ≡ true → hits ξ x y z ≡ true
  back h = hits-intro ξ x y z (λ w →
    trans (sym (same w)) (hits-elim (set0 i ξ) x y z h w))

  flip : ∀ c → (c ≡ true → hits ξ x y z ≡ true) →
         hits ξ x y z ≡ false → c ≡ false
  flip false _ _ = refl
  flip true  f h = contradiction (trans (sym h) (f refl)) λ ()

  go : ∀ b → hits ξ x y z ≡ b → hits (set0 i ξ) x y z ≡ b
  go true  h = hits-intro (set0 i ξ) x y z (λ w →
    trans (same w) (hits-elim ξ x y z h w))
  go false h = flip (hits (set0 i ξ) x y z) back h

amp-set0 : (ξ : PathSum n k m) (i : Fin n) (x z : Assign n) →
           x i ≡ false → amp (set0 i ξ) x z ≐ amp ξ x z
amp-set0 ξ i x z x₀ = Σᴮ-cong (λ y j →
  cong₂ (λ b e → (if b then zpow e else 0ᴬ) j)
        (hits-set0 ξ i x y z x₀) (eval-set0 (phase ξ) i x y x₀))


------------------------------------------------------------------------
-- Equivalence on the inputs where an ancilla is 0

infix 4 _≋[_]₀_

_≋[_]₀_ : PathSum n k m → Fin n → PathSum n k′ m′ → Set
_≋[_]₀_ {k = k} {k′ = k′} ξ i ζ =
  ∀ x z → x i ≡ false → scale k′ (amp ξ x z) ≐ scale k (amp ζ x z)

-- Full equivalence implies it.

≋⇒≋[]₀ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} (i : Fin n) →
         ξ ≋ ζ → ξ ≋[ i ]₀ ζ
≋⇒≋[]₀ i eq x z _ = eq x z

-- What is proved of the path-sum with the ancilla set to 0 holds of
-- the path-sum on those inputs.

set0-≋ : (i : Fin n) (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
         set0 i ξ ≋ ζ → ξ ≋[ i ]₀ ζ
set0-≋ {k′ = k′} i ξ ζ eq x z x₀ j = trans
  (sym (scale-map k′ (amp-set0 ξ i x z x₀) j)) (eq x z j)


------------------------------------------------------------------------
-- Leaving the ancilla clean

private
  scale-0ᴬ : ∀ j → scale j 0ᴬ ≐ 0ᴬ
  scale-0ᴬ zero    i = refl
  scale-0ᴬ (suc j) i = trans (√2·-map (scale-0ᴬ j) i) (√2·-0ᴬ i)

-- If ζ always outputs 0 on qubit i, no path of ζ reaches an output
-- with z_i = 1, so neither does ξ from an input with x_i = 0.

clean-ancilla : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} (i : Fin n) →
                ξ ≋[ i ]₀ ζ →
                (∀ (x : Assign n) (y : Assign m′) → eval (out ζ i) x y ≡ 0ℤ) →
                ∀ x z → x i ≡ false → z i ≡ true → amp ξ x z ≐ 0ᴬ
clean-ancilla {k = k} {k′ = k′} {m′ = m′} {ξ = ξ} {ζ} i eq out0 x z x₀ z₁ =
  scale-injective k′ (amp ξ x z) 0ᴬ (λ j →
    trans (eq x z x₀ j)
      (trans (scale-map k amp0 j)
             (trans (scale-0ᴬ k j) (sym (scale-0ᴬ k′ j)))))
  where
  miss : ∀ y → hits ζ x y z ≡ false
  miss y = flip (hits ζ x y z) λ h →
    trans (sym (cong (λ e → not ⌊ (+ 2) ∣? e ⌋) (out0 x y)))
          (trans (hits-elim ζ x y z h i) z₁)
    where
    flip : ∀ c → (c ≡ true → false ≡ true) → c ≡ false
    flip false _ = refl
    flip true  f = contradiction (f refl) λ ()

  amp0 : amp ζ x z ≐ 0ᴬ
  amp0 j = trans
    (Σᴮ-cong (λ y j′ →
       cong (λ b → (if b then zpow (eval (phase ζ) x y) else 0ᴬ) j′)
            (miss y)) j)
    (Σᴮ-0 {m′} j)
