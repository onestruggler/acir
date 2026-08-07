{-# OPTIONS --cubical-compatible #-}

module Scratch where

open import Data.Nat using (ℕ ; zero)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Product using (_,_ ; proj₁)
open import Data.Vec using (_∷_ ; [])
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; wmap)

open import Examples.Groups.Clifford.Qubit.PrimitiveRoot using (p-2 ; p-prime ; g* ; g-gen)

open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime using (module Symplectic)
open Symplectic using (Gen ; gate₁ ; gate₂ ; H-gate ; S-gate ; CZ-gate ; _↥ ; S ; H ; CZ ; S⁻¹ ; _↑ ; M ; S^)

open import Examples.Groups.Clifford.Qubit.Presentation
  using (PauliGen ; conj ; corr ; vecToWord ; genToVec)
open import Examples.Groups.Pauli.Semantics p-2 p-prime using (pIₙ ; pX ; pZ ; pI ; Pauli)

open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
  using (module Simplified-Relations)
open Simplified-Relations using (M₋₁ ; Mg ; Mg^)

import Examples.Groups.Symplectic.Semantics p-2 p-prime as SympSem
open SympSem.Interpretation using (actg)

-- p reduces
q1 : p ≡ 2
q1 = Eq.refl

-- actg on a generic tail
q5 : ∀ {n} (ps : Pauli n) → actg (gate₁ H-gate) (pI ∷ ps) ≡ pI ∷ ps
q5 ps = Eq.refl

q6 : ∀ {n} (ps : Pauli n) → actg (gate₁ S-gate) (pI ∷ ps) ≡ pI ∷ ps
q6 ps = Eq.refl

q7 : ∀ {n} (ps : Pauli n) → actg (gate₁ H-gate) (pX ∷ ps) ≡ pZ ∷ ps
q7 ps = Eq.refl

q8 : ∀ {n} (ps : Pauli n) → actg (gate₁ H-gate) (pZ ∷ ps) ≡ pX ∷ ps
q8 ps = Eq.refl

q9 : ∀ {n} (ps : Pauli n) → actg (gate₁ S-gate) (pX ∷ ps) ≡ (₁ , ₁) ∷ ps
q9 ps = Eq.refl

q10 : ∀ {n} (ps : Pauli n) → actg (gate₁ S-gate) (pZ ∷ ps) ≡ pZ ∷ ps
q10 ps = Eq.refl

q11 : ∀ {n} (ps : Pauli n) → actg (gate₂ CZ-gate) (pX ∷ pI ∷ ps) ≡ pX ∷ pZ ∷ ps
q11 ps = Eq.refl

q12 : ∀ {n} (ps : Pauli n) → actg (gate₂ CZ-gate) (pZ ∷ pI ∷ ps) ≡ pZ ∷ pI ∷ ps
q12 ps = Eq.refl

q13 : ∀ {n} (ps : Pauli n) → actg (gate₂ CZ-gate) (pI ∷ pX ∷ ps) ≡ pZ ∷ pX ∷ ps
q13 ps = Eq.refl

q14 : ∀ {n} (ps : Pauli n) → actg (gate₂ CZ-gate) (pI ∷ pZ ∷ ps) ≡ pI ∷ pZ ∷ ps
q14 ps = Eq.refl

q15 : ∀ {n} (ps : Pauli n) → actg (gate₂ CZ-gate) (pI ∷ pI ∷ ps) ≡ pI ∷ pI ∷ ps
q15 ps = Eq.refl

-- M at a variable width
q16 : ∀ {n} → M₋₁ {n} ≡ S • H • S • H • S • H
q16 = Eq.refl

q17 : ∀ {n} → Mg {n} ≡ S • H • S • H • S • H
q17 = Eq.refl

-- M-power's right-hand side
module PM' = PrimeModulus' p-2 p-prime
module PR = PM'.Primitive-Root-Modp' g* g-gen

q18 : ∀ {n} → M {n} (PR.g^ ₀) ≡ S • H • S • H • S • H
q18 = Eq.refl

q19 : ∀ {n} → M {n} (PR.g^ ₁) ≡ S • H • S • H • S • H
q19 = Eq.refl

q20 : ∀ {n} → Mg^ ₀ {n} ≡ ε
q20 = Eq.refl

q21 : ∀ {n} → Mg^ ₁ {n} ≡ S • H • S • H • S • H
q21 = Eq.refl

-- semi-MS' right-hand side exponent
q22 : ∀ {n} → S^ {n} (proj₁ g* * proj₁ g*) ≡ S
q22 = Eq.refl

q23 : ∀ {n} → S⁻¹ {n} ≡ S
q23 = Eq.refl
