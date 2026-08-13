{-# OPTIONS --cubical-compatible --safe #-}

open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Product using (_,_ ; proj₁)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
import Data.Nat as Nat
open import Data.Vec hiding ([_])
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥-elim)

open import Word.Base hiding (wfoldl ; _^'_)
open import Notations
open import Data.Nat.Primality

module Examples.Groups.Symplectic.Normalization.Section (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)
open import Examples.Groups.Symplectic.Normalization.Boxes p-2 p-prime public

private
  variable
    n : ℕ

-- A box is MC.
[_]ᵃ : ∀ {n} → A → Word (Gen (₁₊ n))
[_]ᵃ {n} ((₀ , ₀), pr) = ⊥-elim (pr auto)
[_]ᵃ {n} ((₀ , b@(₁₊ b-1)), pr) = XM (b , λ ())
[_]ᵃ {n} ((a@(₁₊ a-1) , b), pr) = XM (a , λ ()) • H • S^ -b/a
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹

[_]ᵇ : ∀ {n} → B → Word (Gen (₂₊ n))
[_]ᵇ {n} (₀ , b) = Ex • CX'^ b
[_]ᵇ {n} (a@(₁₊ a-1) , b) = Ex • CX'^ a • H ↑ • S^ -b/a ↑
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹


[_]ᵈ : ∀ {n} → D → Word (Gen (₂₊ n))
[_]ᵈ {n} (₀ , b) = Ex • CZ^ (- b)
[_]ᵈ {n} (a@(₁₊ _) , b) = Ex • CZ^ (- a) • H • S^ -b/a
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹

[_]ᵉ : ∀ {n} → E → Word (Gen (₁₊ n))
[_]ᵉ {n} b = S^ (- b)

-- Vec B is in circuit order, i.e. the matrix of B1 B2 B3 is B3 * B2 *
-- B1. A reversion is needed for it to be interpreted as words.
[_]ᵛᵇ : ∀ {n} → Vec B n → Word (Gen (₁₊ n))
[_]ᵛᵇ {₀} [] = ε
[_]ᵛᵇ {₁₊ n} (x ∷ v) = [ v ]ᵛᵇ ↑ • [ x ]ᵇ

[_]ᵛᵈ : ∀ {n} → Vec D n → Word (Gen (₁₊ n))
[_]ᵛᵈ {₀} [] = ε
[_]ᵛᵈ {₁₊ n} (x ∷ v) = [ x ]ᵈ • [ v ]ᵛᵈ ↑

[_]ᵐ : ∀ {n} → M n → Word (Gen n)
[_]ᵐ {0} _ = ε
[_]ᵐ {₁₊ n} ([] , e) = [ e ]ᵉ
[_]ᵐ {₁₊ n} (x ∷ vd , e) = [ x ]ᵈ • [ vd , e ]ᵐ ↑

jth-abox : ∀ {j n} → j ≤ n → A → Word (Gen (₁₊ n))
jth-abox {₀} {n} _ a = [ a ]ᵃ
jth-abox {₁₊ j} {₁₊ n} (s≤s j≤n) a = jth-abox {j} {n} (j≤n) a ↑

jth-bbox : ∀ {j n} → j ≤ n → B → Word (Gen (₂₊ n))
jth-bbox {₀} {n} _ a = [ a ]ᵇ
jth-bbox {₁₊ j} {₁₊ n} (s≤s j≤n) a = jth-bbox {j} {n} (j≤n) a ↑

jth-dbox : ∀ {j n} → j ≤ n → B → Word (Gen (₂₊ n))
jth-dbox {₀} {n} _ a = [ a ]ᵈ
jth-dbox {₁₊ j} {₁₊ n} (s≤s j≤n) a = jth-dbox {j} {n} (j≤n) a ↑

jth-ebox : ∀ {j n} → j ≤ n → E → Word (Gen (₁₊ n))
jth-ebox {₀} {n} _ a = [ a ]ᵉ
jth-ebox {₁₊ j} {₁₊ n} (s≤s j≤n) a = jth-ebox {j} {n} (j≤n) a ↑

jth-bboxes : ∀ {j n} → j ≤ n → Vec B (n ∸ j) → Word (Gen (₁₊ n))
jth-bboxes {₀} {n} j≤n v = [ v ]ᵛᵇ
jth-bboxes {₁₊ j} {₁₊ n} (s≤s j≤n) (v) = jth-bboxes j≤n v ↑

lemma-jth-bboxes : ∀ {n} (vb : Vec B n) → jth-bboxes (z≤n {n}) vb ≡ [ vb ]ᵛᵇ
lemma-jth-bboxes {₀} vb = auto
lemma-jth-bboxes {₁₊ j} vb = auto

jth-babox : ∀ {j n} → j ≤ n → Vec B (n ∸ j) → A → Word (Gen (₁₊ n))
jth-babox {₀} {n} j≤n v a = [ v ]ᵛᵇ • jth-abox j≤n a
jth-babox {₁₊ j} {₁₊ n} (s≤s j≤n) v a = jth-babox j≤n v a ↑

[_]ˡ : ∀ {n} → L n → Word (Gen n)
[_]ˡ {0} _ = ε
[_]ˡ {1} a = [ a ]ᵃ
[_]ˡ {₂₊ n} ((j , j≤n) , bs , a) = jth-babox j≤n bs a

[_]ˡ' : ∀ {n} → L' n → Word (Gen n)
[_]ˡ' {0} l = ε
[_]ˡ' {₁₊ n} (vb , a) = [ vb ]ᵛᵇ • [ a ]ᵃ

[_]ᵐˡ' : ∀ {n} → ML' n → Word (Gen n)
[_]ᵐˡ' {0} _ = ε
[_]ᵐˡ' {₁₊ n} (m , l) = [ m ]ᵐ • [ l ]ˡ'

[_]ᵐˡ : ∀ {n} → ML n → Word (Gen n)
[_]ᵐˡ {0} _ = ε
[_]ᵐˡ {1} (m , l) = [ m ]ᵐ • [ l ]ˡ'
[_]ᵐˡ {₂₊ n} (inj₁ (m , l)) = [ m ]ᵐ • [ l ]ˡ'
[_]ᵐˡ {₂₊ n} (inj₂ (d , lm)) = [ d ]ᵈ • [ lm ]ᵐˡ ↑

[_] : ∀ {n} → NF n → Word (Gen n)
[_] {0} tt = ε
[_] {₁₊ n} (nf , lm) = [ nf ] ↑ • [ lm ]ᵐˡ

data BoxType : Set where
  ᵃ : BoxType
  ᵇ : BoxType
  ᵈ : BoxType
  ᵉ : BoxType
  ˡ : BoxType
  ˡ' : BoxType
  ᵐ : BoxType
  ᵐˡ : BoxType
  ᵛᵇ : BoxType
  ᵛᵈ : BoxType
  ⁿᶠ : BoxType

Box : ∀ {n : ℕ} → BoxType → Set
Box ᵃ = A
Box ᵇ = B
Box ᵈ = D
Box ᵉ = E
Box {n} ˡ = L n
Box {n} ˡ' = L' n
Box {n} ᵐ = M n
Box {n} ᵐˡ = ML n
Box {n} ᵛᵇ = Vec B n
Box {n} ᵛᵈ = Vec D n
Box {n} ⁿᶠ = NF n

BIndex : BoxType → Rel ℕ 0ℓ
BIndex ᵃ = _≤_
BIndex ᵉ = _≤_
BIndex ᵇ = _<_
BIndex ᵈ = _<_
BIndex _ = \ _ _ → ⊤

BWidth : BoxType → ℕ
BWidth ⁿᶠ = 0
BWidth ˡ = 0
BWidth ˡ' = 0
BWidth ᵐ = 0
BWidth ᵐˡ = 0
BWidth ᵇ = 2
BWidth ᵈ = 2
BWidth _ = 1

-- A unified way to call all box interpretation.
⟦_⟧ : ∀ {j n} (bt : BoxType) → Box {n} bt → BIndex bt j n → Word (Gen (BWidth bt Nat.+ n))
⟦_⟧ {j} {n} ᵃ x j≤n = jth-abox j≤n x
⟦_⟧ {j} {₁₊ n} ᵇ x j<n = jth-bbox j<n x
⟦_⟧ {j} {n} ᵈ x j<n = jth-dbox j<n x
⟦_⟧ {j} {n} ᵉ x j≤n = jth-ebox j≤n x
⟦_⟧ {j} {n} ˡ x j≤n = [ x ]ˡ
⟦_⟧ {j} {n} ˡ' x j≤n = [ x ]ˡ'
⟦_⟧ {j} {n} ᵐ x j≤n = [ x ]ᵐ
⟦_⟧ {j} {n} ᵐˡ x j≤n = [ x ]ᵐˡ
⟦_⟧ {j} {n} ᵛᵇ x j≤n = [ x ]ᵛᵇ
⟦_⟧ {j} {n} ᵛᵈ x j≤n = [ x ]ᵛᵈ
⟦_⟧ {j} {n} ⁿᶠ x j≤n = [ x ]
