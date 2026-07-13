------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger step 1 (§3): the Clifford action on the Pauli group.
--
-- The semantic model of a Clifford word is its conjugation action on the
-- ℤ/4-phased Pauli group P4 (= Selinger's P(n) modulo the global scalar
-- ω), namely `cact` from CliffordAction.  Soundness of the Figure-8
-- relations w.r.t. this action both establishes that Figure 8 presents (a
-- quotient of) the Clifford group and validates the transcription.
--
-- This file proves soundness of the "order" relations C2 (H²=1), C3
-- (S⁴=1) and C5 (CZ²=1); the two-qubit and three-qubit relations follow
-- in later files.  (C1/C4, being purely about the scalar ω, are invisible
-- to the ℤ/4 action and are validated by the ℤ/8 layer.)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger.Action where

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime ; prime?)
open import Data.Product using (_,_)
open import Data.Vec using (_∷_)
open import Relation.Nullary.Decidable using (from-yes)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Zp.ModularArithmetic
open import Word.Base using (_^_)

p-2 : ℕ
p-2 = 0

p-prime : Prime 2
p-prime = from-yes (prime? 2)

open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime
  using (module Symplectic-Derived-Gen)
open Symplectic-Derived-Gen using (Gen ; gate₁ ; gate₂ ; H-gen ; S-gen ; CZ-gen ; S ; H ; CZ ; _↑ ; _↓)

open import Examples.Groups.Clifford.Qubit.SignedPauli using (P4Carrier ; ι)
open import Examples.Groups.Clifford.Qubit.CliffordAction using (cact ; cact1 ; δ ; incl)
open import Word.Base using (_•_)
open import Examples.Groups.Clifford.Qubit.CliffordAut using (g4-id ; ι-2 ; neg-id ; neg-mul)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- C3:  S⁴ = 1.  Exactly g4-id at the S generator.

c3-sound : (x : P4Carrier (₁₊ n)) → cact (S ^ 4) x ≡ x
c3-sound = g4-id (gate₁ (S-gen ₁))

------------------------------------------------------------------------
-- C2:  H² = 1.  H has P4-order 2 (H² = I on P4, phase included).

c2-sound : (x : P4Carrier (₁₊ n)) → cact (H ^ 2) x ≡ x
c2-sound (s , (a , b) ∷ ps) = Eq.cong₂ _,_ phase pauli
  where
  open Eq.≡-Reasoning
  -- phase: s + ι(₁·a·b) + ι(₁·(-b)·a) ≡ s, the two ι's cancelling.
  phase : (s + ι (₁ * a * b)) + ι (₁ * (- b) * a) ≡ s
  phase = begin
    (s + ι (₁ * a * b)) + ι (₁ * (- b) * a)
      ≡⟨ +-assoc s (ι (₁ * a * b)) (ι (₁ * (- b) * a)) ⟩
    s + (ι (₁ * a * b) + ι (₁ * (- b) * a))
      ≡⟨ Eq.cong (λ □ → s + (ι (₁ * a * b) + ι □)) lemma ⟩
    s + (ι (₁ * a * b) + ι (₁ * a * b))
      ≡⟨ Eq.cong (s +_) (ι-2 (₁ * a * b)) ⟩
    s + ₀   ≡⟨ +-identityʳ s ⟩   s ∎
    where
    -- ₁·(-b)·a = ₁·a·b, using -x=x and commutativity at p=2.
    lemma : ₁ * (- b) * a ≡ ₁ * a * b
    lemma = begin
      ₁ * (- b) * a   ≡⟨ Eq.cong (λ □ → ₁ * □ * a) (neg-id b) ⟩
      ₁ * b * a       ≡⟨ *-assoc ₁ b a ⟩
      ₁ * (b * a)     ≡⟨ Eq.cong (₁ *_) (*-comm b a) ⟩
      ₁ * (a * b)     ≡⟨ Eq.sym (*-assoc ₁ a b) ⟩
      ₁ * a * b       ∎
  pauli : ((- a) , (- b)) ∷ ps ≡ (a , b) ∷ ps
  pauli = Eq.cong (_∷ ps) (Eq.cong₂ _,_ (neg-id a) (neg-id b))

------------------------------------------------------------------------
-- C5:  CZ² = 1.  CZ has P4-order 2.

-- v + v = 0 at p = 2.
x+x : (v : ℤ ₚ) → v + v ≡ ₀
x+x ₀ = Eq.refl
x+x ₁ = Eq.refl

c5-sound : (x : P4Carrier (₂₊ n)) → cact (CZ ^ 2) x ≡ x
c5-sound (s , (a , b) ∷ (a' , b') ∷ ps) = Eq.cong₂ _,_ phase pauli
  where
  open Eq.≡-Reasoning
  phase : (s + ι (₁ * a * a')) + ι (₁ * a * a') ≡ s
  phase = begin
    (s + ι (₁ * a * a')) + ι (₁ * a * a')
      ≡⟨ +-assoc s (ι (₁ * a * a')) (ι (₁ * a * a')) ⟩
    s + (ι (₁ * a * a') + ι (₁ * a * a'))
      ≡⟨ Eq.cong (s +_) (ι-2 (₁ * a * a')) ⟩
    s + ₀   ≡⟨ +-identityʳ s ⟩   s ∎
  pauli : (a , b + a' * ₁ + a' * ₁) ∷ (a' , b' + a * ₁ + a * ₁) ∷ ps
        ≡ (a , b) ∷ (a' , b') ∷ ps
  pauli = Eq.cong₂ (λ □ ▢ → (a , □) ∷ (a' , ▢) ∷ ps)
            (Eq.trans (+-assoc b (a' * ₁) (a' * ₁)) (Eq.trans (Eq.cong (b +_) (x+x (a' * ₁))) (+-identityʳ b)))
            (Eq.trans (+-assoc b' (a * ₁) (a * ₁)) (Eq.trans (Eq.cong (b' +_) (x+x (a * ₁))) (+-identityʳ b')))

------------------------------------------------------------------------
-- C6/C7:  S commutes with CZ (either wire).

-- Swap the last two summands: (s + x) + y ≡ (s + y) + x.
swap-add : ∀ {m} (s x y : ℤ m) → (s + x) + y ≡ (s + y) + x
swap-add s x y = Eq.trans (+-assoc s x y)
                 (Eq.trans (Eq.cong (s +_) (+-comm x y))
                           (Eq.sym (+-assoc s y x)))

-- C6:  S↓·CZ = CZ·S↓.  S on wire 0 is diagonal, hence commutes with CZ;
-- on the action the two conjugation phases and the two Z-updates just
-- swap order.
c6-sound : (x : P4Carrier (₂₊ n)) → cact (S ↓ • CZ) x ≡ cact (CZ • S ↓) x
c6-sound (s , (a , b) ∷ (a' , b') ∷ ps) = Eq.cong₂ _,_
  (swap-add s (ι (₁ * a * a')) (incl (₁ * a)))
  (Eq.cong (λ □ → (a , □) ∷ (a' , b' + a * ₁) ∷ ps) (swap-add b (a' * ₁) (a * ₁)))

-- C7:  S↑·CZ = CZ·S↑.  Same, with the roles of the two wires exchanged.
c7-sound : (x : P4Carrier (₂₊ n)) → cact (S ↑ • CZ) x ≡ cact (CZ • S ↑) x
c7-sound (s , (a , b) ∷ (a' , b') ∷ ps) = Eq.cong₂ _,_
  (swap-add s (ι (₁ * a * a')) (incl (₁ * a')))
  (Eq.cong (λ □ → (a , b + a' * ₁) ∷ (a' , □) ∷ ps) (swap-add b' (a * ₁) (a' * ₁)))
