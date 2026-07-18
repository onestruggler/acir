{-# OPTIONS --cubical-compatible --safe #-}
--{-# OPTIONS  --call-by-name #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; module ≡-Reasoning)
import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Data.Vec hiding ([_])
open import Data.Empty using (⊥-elim)

open import Word.Base hiding (wfoldl ; _^'_)
import Presentation.Base as PB
open import Notations
open import Data.Nat.Primality



module Examples.Groups.Symplectic.ExtendedGate.Semantics.ActionLemmas (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where


open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Cosets p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime
open Symplectic-Derived-Gen renaming (M to ZM)
open import Examples.Groups.Symplectic.ExtendedGate.NF1 p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Normalization.Section p-2 p-prime public
open Normal-Form1

open import Examples.Groups.Symplectic.ExtendedGate.NF2 p-2 p-prime
open LM2

private
  variable
    n : ℕ


-- The maps from boxes to Word (Gen n) — including the section map [_] and
-- the unified interpreter ⟦_⟧ — live in
-- Examples.Groups.Symplectic.ExtendedGate.Normalization.Section (re-exported above).

--open import Examples.Groups.Pauli.Semantics p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Properties p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Soundness p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)

sfrom-pIq=0 : ∀ x -> sform1 pI x ≡ ₀
sfrom-pIq=0 x@(c , d) = begin
  sform1 pI x ≡⟨ auto ⟩
  - ₀ * d + c * ₀ ≡⟨ Eq.cong₂ (\ xx yy -> xx * d + yy) -0#≈0# (*-zeroʳ c) ⟩
  ₀ * d + ₀ ≡⟨ +-identityʳ (₀ * d) ⟩
  ₀ * d ≡⟨ *-zeroˡ d ⟩
  ₀ ∎
  where
  open ≡-Reasoning


lemma-act-CX : ∀ (p@(a , b) q@(c , d) : Pauli1) t ->
  act {₂₊ n} CX (p ∷ q ∷ t) ≡ ((a + c , b) ∷ (c , d + - b) ∷ t)
lemma-act-CX p@(a , b) q@(c , d) t = begin
  act (H ^ ₃ • CZ • H) ((a , b) ∷ (c , d) ∷ t) ≡⟨ auto ⟩
  act (H ^ ₃ • CZ) ((- b , a) ∷ (c , d) ∷ t) ≡⟨ auto ⟩
  act (H ^ ₃) ((- b , a + c * ₁) ∷ (c , d + - b * ₁) ∷ t) ≡⟨  Eq.cong₂ (\ xx yy -> act (H ^ ₃) ((- b , a + xx) ∷ (c , d + yy) ∷ t)) (*-identityʳ (c)) (*-identityʳ (- b))  ⟩
  act (H ^ ₃) ((- b , a + c) ∷ (c , d + - b) ∷ t) ≡⟨ act-sound _ _ (PB.sym (PB.axiom (srel (derived-H ₃)))) (((- b , a + c) ∷ (c , d + - b) ∷ t)) ⟩
  act (H^ ₃) ((- b , a + c) ∷ (c , d + - b) ∷ t) ≡⟨ auto ⟩
  ((a + c , - - b) ∷ (c , d + - b) ∷ t) ≡⟨ Eq.cong (\ xx -> ((a + c , xx) ∷ (c , d + - b) ∷ t)) (-‿involutive b) ⟩
  ((a + c , b) ∷ (c , d + - b) ∷ t) ∎
  where
  open ≡-Reasoning


lemma-act-Ex : ∀ p q t ->
  act {₂₊ n} Ex (p ∷ q ∷ t) ≡ (q ∷ p ∷ t)
lemma-act-Ex p q t = act-Ex (p .proj₁) (p .proj₂) (q .proj₁) (q .proj₂) t

-- lemma-abox' : ∀ (ab@((a , b), neqI) : A) t ->
--   act [ (a , b) , neqI ]ᵃ ((a , b) ∷ t) ≡ {!!}

lemma-abox-01 : ∀ (ps : Pauli (₁₊ n)) →
  act [ (₀ , ₁) , (λ ()) ]ᵃ ps ≡ ps
lemma-abox-01 ps@((a , b) ∷ t) = begin
  act [ (₀ , ₁) , (λ ()) ]ᵃ ps ≡⟨ auto ⟩
  act ⟦ (₁ , λ ()) ⁻¹ , ε ⟧ₘ₊ ps ≡⟨ auto ⟩
  act ⟦ (₁ , λ ()) ⁻¹ ⟧ₘ ps ≡⟨ lemma-M a b t ((₁ , λ ()) ⁻¹) ⟩
  (a * x⁻¹ , b * x) ∷ t ≡⟨ Eq.cong₂ (λ xx yy → (a * xx , b * yy) ∷ t) aux-inv1 inv-₁ ⟩
  (a * ₁ , b * ₁) ∷ t ≡⟨ Eq.cong₂ (\ xx yy -> (xx , yy) ∷ t) (*-identityʳ a) (*-identityʳ b) ⟩
  ps ∎
  where
  open ≡-Reasoning
  x' = (₁ , λ ()) ⁻¹
  x = (x' .proj₁)
  x⁻¹ = ((x' ⁻¹) .proj₁)
  aux-inv1 : x⁻¹ ≡ ₁
  aux-inv1 = Eq.trans (inv-cong (x' ) ((₁ , λ ())) inv-₁) inv-₁
  


lemma-abox : ∀ p (neqI : p ≢ pI)(ps : Pauli n) →
  act [ p , neqI ]ᵃ (p ∷ ps) ≡ (pZ ∷ ps)
lemma-abox (₀ , ₀) neqI ps = ⊥-elim (neqI auto)
lemma-abox (₀ , b@(₁₊ b')) neqI ps = begin
  act ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊ ((₀ , ₁₊ b') ∷ ps) ≡⟨ auto ⟩
  act ⟦ (b , λ ()) ⁻¹ ⟧ₘ ((₀ , ₁₊ b') ∷ ps) ≡⟨ lemma-M ₀ b ps ((b , λ ()) ⁻¹) ⟩
  (₀ * x⁻¹ , (₁₊ b') * x) ∷ ps ≡⟨ Eq.cong₂ (\ xx yy -> (xx , yy) ∷ ps) (*-zeroˡ x⁻¹) (lemma-⁻¹ʳ b {{nztoℕ {y = b} {neq0 = λ ()}}}) ⟩
  pZ ∷ ps ∎
  where
  open ≡-Reasoning
  x = ((b , λ ()) ⁻¹) .proj₁
  x⁻¹ = ((b , λ ()) ⁻¹ ⁻¹) .proj₁
  
lemma-abox (a@(₁₊ a') , b) neqI ps = begin
  act ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ ((a , b) ∷ ps) ≡⟨ auto ⟩
  act ⟦ (a , λ ()) ⁻¹ ⟧ₘ (act ⟦ HS^ -b/a ⟧ₕₛ ((a , b) ∷ ps)) ≡⟨ Eq.cong (act ⟦ (a , λ ()) ⁻¹ ⟧ₘ) (lemma-HS-x -b/a a b ps) ⟩
  act ⟦ (a , λ ()) ⁻¹ ⟧ₘ ((- (b + a * -b/a) , a) ∷ ps) ≡⟨ Eq.cong (\ xx -> act ⟦ (a , λ ()) ⁻¹ ⟧ₘ ((xx , a) ∷ ps)) (Eq.trans (Eq.cong -_ aux) -0#≈0#) ⟩
  act ⟦ (a , λ ()) ⁻¹ ⟧ₘ ((₀ , a) ∷ ps) ≡⟨ lemma-M ₀ a ps ((a , λ ()) ⁻¹) ⟩
  (₀ * a⁻¹⁻¹  , a * a⁻¹) ∷ ps ≡⟨ Eq.cong (\ xx -> (₀ * a⁻¹⁻¹  , xx) ∷ ps) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = λ ()}}}) ⟩
  pZ ∷ ps ∎
  where
  open ≡-Reasoning
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  a⁻¹⁻¹ = ((a , λ ()) ⁻¹ ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  aux : b + a * -b/a ≡ ₀
  aux = begin
    b + a * -b/a ≡⟨ Eq.cong (\ xx -> b + a * xx) (*-comm (- b) a⁻¹) ⟩
    b + a * (a⁻¹ * - b) ≡⟨ Eq.cong (b +_) (Eq.sym (*-assoc a a⁻¹ (- b))) ⟩
    b + a * a⁻¹ * - b ≡⟨ Eq.cong (\ xx -> b + xx * - b) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = λ ()}}}) ⟩
    b + ₁ * - b ≡⟨ Eq.cong (b +_) (*-identityˡ (- b)) ⟩
    b + - b ≡⟨ +-inverseʳ b ⟩
    ₀ ∎


lemma-dbox-IZ : ∀ d (t : Pauli n) -> act [ d ]ᵈ (pI ∷ pZ ∷ t) ≡ (pZ ∷ pI ∷ t)
lemma-dbox-IZ {n} (₀ , d) t = begin
  act [ ₀ , d ]ᵈ (pI ∷ pZ ∷ t) ≡⟨ auto ⟩
  act (Ex • CZ^ (- d)) (pI ∷ pZ ∷ t) ≡⟨ auto ⟩
  act Ex (act (CZ^ (- d)) (pI ∷ pZ ∷ t)) ≡⟨ auto ⟩
  act Ex ((₀ , ₀ + ₀ * (- d)) ∷ (₀ , ₁ + ₀ * (- d)) ∷ t) ≡⟨ Eq.cong (\ xx -> act Ex ((₀ , ₀ + xx) ∷ (₀ , ₁ + xx) ∷ t)) (*-zeroˡ (- d)) ⟩
  act Ex ((₀ , ₀ + ₀) ∷ (₀ , ₁ + ₀) ∷ t) ≡⟨ lemma-act-Ex pI pZ t ⟩
  (pZ ∷ pI ∷ t) ∎
  where
  open ≡-Reasoning

lemma-dbox-IZ {n} (c@(₁₊ c') , d) t = begin
  act [ ₁₊ c' , d ]ᵈ (pI ∷ pZ ∷ t) ≡⟨ auto ⟩
  act ([ ₀ , ₁ ]ᵈ • [ (₁₊ c' , d) , (λ ()) ]ᵃ) (pI ∷ pZ ∷ t) ≡⟨ auto ⟩
  act ([ ₀ , ₁ ]ᵈ • ⟦ (₁₊ c' , λ ()) ⁻¹ , HS^ -d/c ⟧ₘ₊) (pI ∷ pZ ∷ t) ≡⟨ Eq.cong (act ([ ₀ , ₁ ]ᵈ • ⟦ (₁₊ c' , λ ()) ⁻¹ ⟧ₘ)) (lemma-HS-x -d/c ₀ ₀ (pZ ∷ t)) ⟩
  act ([ ₀ , ₁ ]ᵈ • ⟦ (₁₊ c' , λ ()) ⁻¹ ⟧ₘ) ((- (₀ + ₀ * -d/c) , ₀) ∷ pZ ∷ t) ≡⟨ Eq.cong (act ([ ₀ , ₁ ]ᵈ • ⟦ (₁₊ c' , λ ()) ⁻¹ ⟧ₘ)) aux2 ⟩
  act ([ ₀ , ₁ ]ᵈ • ⟦ (₁₊ c' , λ ()) ⁻¹ ⟧ₘ) ((₀ , ₀) ∷ pZ ∷ t) ≡⟨ (Eq.cong (act ([ ₀ , ₁ ]ᵈ)) (lemma-M ₀ ₀ (pZ ∷ t) ((₁₊ c' , λ ()) ⁻¹))) ⟩
  act ([ ₀ , ₁ ]ᵈ) ((₀ * c⁻¹⁻¹ , ₀ * c⁻¹) ∷ pZ ∷ t) ≡⟨ (Eq.cong₂ (\ xx yy -> act ([ ₀ , ₁ ]ᵈ) ((xx , yy) ∷ pZ ∷ t)) (*-zeroˡ c⁻¹⁻¹) (*-zeroˡ c⁻¹)) ⟩
  act ([ ₀ , ₁ ]ᵈ) ((₀ , ₀) ∷ pZ ∷ t) ≡⟨ auto ⟩
  act Ex ((₀ , ₀ + ₀ * - ₁) ∷ (₀ , ₁ + ₀ * - ₁) ∷ t) ≡⟨ Eq.cong (\ xx -> act Ex ((₀ , ₀ + xx) ∷ (₀ , ₁ + xx) ∷ t)) (*-zeroˡ (- ₁)) ⟩
  act Ex ((₀ , ₀) ∷ (₀ , ₁ + ₀) ∷ t) ≡⟨ lemma-act-Ex pI pZ t ⟩
  (pZ ∷ pI ∷ t) ∎
  where
  open ≡-Reasoning
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  c⁻¹⁻¹ = ((c , λ ()) ⁻¹ ⁻¹) .proj₁
  -d/c = - d * c⁻¹
  aux : - (₀ + ₀ * -d/c) ≡ ₀
  aux = begin
    - (₀ + ₀ * -d/c) ≡⟨ Eq.cong -_ (Eq.cong (₀ +_) (*-zeroˡ -d/c)) ⟩
    - (₀ + ₀) ≡⟨ -0#≈0# ⟩
    ₀ ∎
  aux2 : _≡_ {A = Pauli (₂₊ n)} ((- (₀ + ₀ * -d/c) , ₀) ∷ pZ ∷ t) ((₀ , ₀) ∷ pZ ∷ t)
  aux2 = (Eq.cong (\ (xx : ℤ ₚ) -> (xx , ₀) ∷ pZ ∷ t) aux )

