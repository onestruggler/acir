------------------------------------------------------------------------
-- Presentations of groups
--
-- The Clifford group as automorphisms of P4 (p = 2), stage 2b: cact1 g is
-- a group homomorphism of P4.
--
-- cact1 g (s , P) = (s + δ g P , act1 g P) is a homomorphism of P4 because
--   * act1 g is additive on the Pauli part (act1-+), and
--   * δ g is a quadratic refinement of the symplectic form: its
--     polarisation matches the change of the commutation cocycle γ under
--     act1 g (δ-coc).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Examples.Groups.Clifford.Qubit.CliffordAut where

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime ; prime?)
open import Data.Product using (_×_ ; _,_)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Nullary.Decidable using (from-yes)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Zp.ModularArithmetic

p-2 : ℕ
p-2 = 0

p-prime : Prime 2
p-prime = from-yes (prime? 2)

open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2) using (-‿+-comm)

open import Examples.Groups.Pauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; _+ₚ_ ; _+₁_ ; pIₙ)
open import Examples.Groups.Symplectic.Action p-2 p-prime using (act1)
open import Examples.Groups.Symplectic.Symplectic-Derived p-2 p-prime
  using (module Symplectic-Derived-Gen)
open Symplectic-Derived-Gen
  using (Gen ; gate₁ ; gate₂ ; H-gen ; S-gen ; CZ-gen ; _↥)

open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)

open import Examples.Groups.Clifford.Qubit.SignedPauli
  using (Φ ; P4Carrier ; β ; γ ; ι ; ι-+)
open import Examples.Groups.Clifford.Qubit.CliffordAction using (δ ; incl ; cact1)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- ℤ/4 helper identities (both moduli concrete, so mostly by computation)

-- ι has order ≤ 2 in ℤ/4.
ι-2 : (x : ℤ ₚ) → ι x + ι x ≡ ₀
ι-2 ₀ = auto
ι-2 ₁ = auto

-- incl is additive up to the ×2 image of the product.
incl-+ : (a c : ℤ ₚ) → incl a + incl c ≡ incl (a + c) + ι (a * c)
incl-+ ₀ ₀ = auto
incl-+ ₀ ₁ = auto
incl-+ ₁ ₀ = auto
incl-+ ₁ ₁ = auto

-- -x = x at p = 2.
neg-id : (x : ℤ ₚ) → - x ≡ x
neg-id ₀ = auto
neg-id ₁ = auto

-- γ on a cons cell splits off the head commutation b·c and the tail.
γ-cons : ∀ {m} (a b c d : ℤ ₚ) (t t' : Pauli m) →
         γ ((a , b) ∷ t) ((c , d) ∷ t') ≡ ι (b * c) + γ t t'
γ-cons a b c d t t' = ι-+ (b * c) (β t t')

-- Two generic ℤ/4 rearrangements, factoring a common tail term.
app-U : (A U D Y Z : Φ) → A + D ≡ Y + Z → (A + U) + D ≡ Y + (Z + U)
app-U A U D Y Z hyp = begin
  (A + U) + D   ≡⟨ +-assoc A U D ⟩
  A + (U + D)   ≡⟨ Eq.cong (A +_) (+-comm U D) ⟩
  A + (D + U)   ≡⟨ Eq.sym (+-assoc A D U) ⟩
  (A + D) + U   ≡⟨ Eq.cong (_+ U) hyp ⟩
  (Y + Z) + U   ≡⟨ +-assoc Y Z U ⟩
  Y + (Z + U)   ∎
  where open Eq.≡-Reasoning

pre-C : (C A D Y Z : Φ) → A + D ≡ Y + Z → (C + A) + D ≡ Y + (C + Z)
pre-C C A D Y Z hyp = begin
  (C + A) + D   ≡⟨ +-assoc C A D ⟩
  C + (A + D)   ≡⟨ Eq.cong (C +_) hyp ⟩
  C + (Y + Z)   ≡⟨ Eq.sym (+-assoc C Y Z) ⟩
  (C + Y) + Z   ≡⟨ Eq.cong (_+ Z) (+-comm C Y) ⟩
  (Y + C) + Z   ≡⟨ +-assoc Y C Z ⟩
  Y + (C + Z)   ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The head cocycle identity for the S gate (finite, by computation).

HEAD-S : (k a b c : ℤ ₚ) →
  ι (b * c) + incl (k * (a + c)) ≡
  (incl (k * a) + incl (k * c)) + ι ((b + a * k) * c)
HEAD-S ₀ ₀ ₀ ₀ = auto
HEAD-S ₀ ₀ ₀ ₁ = auto
HEAD-S ₀ ₀ ₁ ₀ = auto
HEAD-S ₀ ₀ ₁ ₁ = auto
HEAD-S ₀ ₁ ₀ ₀ = auto
HEAD-S ₀ ₁ ₀ ₁ = auto
HEAD-S ₀ ₁ ₁ ₀ = auto
HEAD-S ₀ ₁ ₁ ₁ = auto
HEAD-S ₁ ₀ ₀ ₀ = auto
HEAD-S ₁ ₀ ₀ ₁ = auto
HEAD-S ₁ ₀ ₁ ₀ = auto
HEAD-S ₁ ₀ ₁ ₁ = auto
HEAD-S ₁ ₁ ₀ ₀ = auto
HEAD-S ₁ ₁ ₀ ₁ = auto
HEAD-S ₁ ₁ ₁ ₀ = auto
HEAD-S ₁ ₁ ₁ ₁ = auto

-- The S-gate clause of δ-coc, stated with the definitional reductions of
-- δ and act1 already applied.
δ-coc-S : ∀ {m} (k a b c d : ℤ ₚ) (ps qs : Pauli m) →
  γ ((a , b) ∷ ps) ((c , d) ∷ qs) + incl (k * (a + c)) ≡
  (incl (k * a) + incl (k * c)) + γ ((a , b + a * k) ∷ ps) ((c , d + c * k) ∷ qs)
δ-coc-S k a b c d ps qs = begin
  γ ((a , b) ∷ ps) ((c , d) ∷ qs) + incl (k * (a + c))
    ≡⟨ Eq.cong (_+ incl (k * (a + c))) (γ-cons a b c d ps qs) ⟩
  (ι (b * c) + γ ps qs) + incl (k * (a + c))
    ≡⟨ app-U (ι (b * c)) (γ ps qs) (incl (k * (a + c)))
             (incl (k * a) + incl (k * c)) (ι ((b + a * k) * c)) (HEAD-S k a b c) ⟩
  (incl (k * a) + incl (k * c)) + (ι ((b + a * k) * c) + γ ps qs)
    ≡⟨ Eq.cong ((incl (k * a) + incl (k * c)) +_)
               (Eq.sym (γ-cons a (b + a * k) c (d + c * k) ps qs)) ⟩
  (incl (k * a) + incl (k * c)) + γ ((a , b + a * k) ∷ ps) ((c , d + c * k) ∷ qs)  ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- act1 g is additive on Pauli exponents

private
  -- The S/CZ coordinate identity:  (b+d) + (a+c)*k ≡ (b + a*k) + (d + c*k).
  aux-S : ∀ (b d a c k : ℤ ₚ) → (b + d) + (a + c) * k ≡ (b + a * k) + (d + c * k)
  aux-S b d a c k = begin
    (b + d) + (a + c) * k         ≡⟨ Eq.cong ((b + d) +_) (*-distribʳ-+ k a c) ⟩
    (b + d) + (a * k + c * k)     ≡⟨ +-assoc b d (a * k + c * k) ⟩
    b + (d + (a * k + c * k))     ≡⟨ Eq.cong (b +_) (Eq.sym (+-assoc d (a * k) (c * k))) ⟩
    b + ((d + a * k) + c * k)     ≡⟨ Eq.cong (λ □ → b + (□ + c * k)) (+-comm d (a * k)) ⟩
    b + ((a * k + d) + c * k)     ≡⟨ Eq.cong (b +_) (+-assoc (a * k) d (c * k)) ⟩
    b + (a * k + (d + c * k))     ≡⟨ Eq.sym (+-assoc b (a * k) (d + c * k)) ⟩
    (b + a * k) + (d + c * k)     ∎
    where open Eq.≡-Reasoning

act1-+ : (g : Gen n) (P P' : Pauli n) →
         act1 g (P +ₚ P') ≡ act1 g P +ₚ act1 g P'
act1-+ (gate₁ (H-gen ₀)) ((a , b) ∷ ps) ((c , d) ∷ qs) = Eq.refl
act1-+ (gate₁ (H-gen ₁)) ((a , b) ∷ ps) ((c , d) ∷ qs) =
  Eq.cong₂ _∷_ (≡×≡⇒≡ (Eq.sym (-‿+-comm b d) , Eq.refl)) Eq.refl
act1-+ (gate₁ (H-gen ₂)) ((a , b) ∷ ps) ((c , d) ∷ qs) =
  Eq.cong₂ _∷_ (≡×≡⇒≡ (Eq.sym (-‿+-comm a c) , Eq.sym (-‿+-comm b d))) Eq.refl
act1-+ (gate₁ (H-gen ₃)) ((a , b) ∷ ps) ((c , d) ∷ qs) =
  Eq.cong₂ _∷_ (≡×≡⇒≡ (Eq.refl , Eq.sym (-‿+-comm a c))) Eq.refl
act1-+ (gate₁ (S-gen k)) ((a , b) ∷ ps) ((c , d) ∷ qs) =
  Eq.cong₂ _∷_ (≡×≡⇒≡ (Eq.refl , aux-S b d a c k)) Eq.refl
act1-+ (gate₂ (CZ-gen k)) ((a , b) ∷ (a' , b') ∷ ps) ((c , d) ∷ (c' , d') ∷ qs) =
  Eq.cong₂ _∷_ (≡×≡⇒≡ (Eq.refl , aux-S b d a' c' k))
    (Eq.cong₂ _∷_ (≡×≡⇒≡ (Eq.refl , aux-S b' d' a c k)) Eq.refl)
act1-+ (g ↥) (p ∷ ps) (q ∷ qs) = Eq.cong₂ _∷_ Eq.refl (act1-+ g ps qs)
