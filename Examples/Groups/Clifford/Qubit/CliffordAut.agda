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

private
  variable
    n : ℕ

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
