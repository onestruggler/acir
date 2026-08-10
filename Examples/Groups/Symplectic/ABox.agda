------------------------------------------------------------------------
-- Presentations of groups
--
-- The A-box clears its own vector to pZ:
--
--   lemma-abox :  act [ (p , pr) ]ᵃ (p ∷ t) ≡ pZ ∷ t
--
-- This is the a-box ingredient of the inj₁ case of Theorem-LM (leading
-- qupit of p nonzero).  Built, like the n=1 case, from act-M / act-HS^.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.ABox (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_×_ ; _,_ ; proj₁)
open import Data.Empty using (⊥-elim)
open import Data.Vec using (_∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_ ; module ≡-Reasoning)

open import Notations
open import Word.Base using (_•_)

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime using (Pauli ; Pauli1 ; sform1 ; pZ ; pI)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic using (M ; H ; S^)

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime using (A ; [_]ᵃ)

open import Examples.Groups.Symplectic.BoxAction p-2 p-prime
  using (act ; act-M ; act-HS^)

private
  variable
    n : ℕ

lemma-abox : ∀ (p : ℤ ₚ × ℤ ₚ) (pr : p ≢ (₀ , ₀)) (t : Pauli n) →
  act [ (p , pr) ]ᵃ (p ∷ t) ≡ pZ ∷ t
lemma-abox (₀ , ₀)     pr t = ⊥-elim (pr Eq.refl)
lemma-abox (₀ , ₁₊ b') pr t = begin
  act (M bb) ((₀ , ₁₊ b') ∷ t)
    ≡⟨ act-M bb ₀ (₁₊ b') t ⟩
  (₀ * (bb ⁻¹) .proj₁ , (₁₊ b') * (bb .proj₁)) ∷ t
    ≡⟨ Eq.cong₂ (λ z w → (z , w) ∷ t) (*-zeroˡ ((bb ⁻¹) .proj₁))
         (lemma-⁻¹ʳ (₁₊ b') {{nztoℕ {y = ₁₊ b'} {neq0 = λ ()}}}) ⟩
  pZ ∷ t ∎
  where
  open ≡-Reasoning
  bb = (₁₊ b' , λ ()) ⁻¹
lemma-abox (₁₊ a' , b) pr t = begin
  act (M aa • (H • S^ (- b * x))) ((₁₊ a' , b) ∷ t)
    ≡⟨ Eq.cong (act (M aa)) (act-HS^ (- b * x) (₁₊ a') b t) ⟩
  act (M aa) ((- (b + (₁₊ a') * (- b * x)) , ₁₊ a') ∷ t)
    ≡⟨ Eq.cong (λ z → act (M aa) ((- z , ₁₊ a') ∷ t)) top=0 ⟩
  act (M aa) ((- ₀ , ₁₊ a') ∷ t)
    ≡⟨ Eq.cong (λ z → act (M aa) ((z , ₁₊ a') ∷ t)) -0#≈0# ⟩
  act (M aa) ((₀ , ₁₊ a') ∷ t)
    ≡⟨ act-M aa ₀ (₁₊ a') t ⟩
  (₀ * (aa ⁻¹) .proj₁ , (₁₊ a') * (aa .proj₁)) ∷ t
    ≡⟨ Eq.cong₂ (λ z w → (z , w) ∷ t) (*-zeroˡ ((aa ⁻¹) .proj₁))
         (lemma-⁻¹ʳ (₁₊ a') {{nztoℕ {y = ₁₊ a'} {neq0 = λ ()}}}) ⟩
  pZ ∷ t ∎
  where
  open ≡-Reasoning
  aa = (₁₊ a' , λ ()) ⁻¹
  x  = ((₁₊ a' , λ ()) ⁻¹) .proj₁
  -- b + (₁₊a')·(-b·x) = b + (-b)·((₁₊a')·x) = b + (-b) = 0.
  top=0 : b + (₁₊ a') * (- b * x) ≡ ₀
  top=0 = begin
    b + (₁₊ a') * (- b * x)     ≡⟨ Eq.cong (b +_) (Eq.sym (*-assoc (₁₊ a') (- b) x)) ⟩
    b + (₁₊ a') * (- b) * x     ≡⟨ Eq.cong (λ z → b + z * x) (*-comm (₁₊ a') (- b)) ⟩
    b + (- b) * (₁₊ a') * x     ≡⟨ Eq.cong (b +_) (*-assoc (- b) (₁₊ a') x) ⟩
    b + (- b) * ((₁₊ a') * x)   ≡⟨ Eq.cong (λ z → b + (- b) * z) (lemma-⁻¹ʳ (₁₊ a') {{nztoℕ {y = ₁₊ a'} {neq0 = λ ()}}}) ⟩
    b + (- b) * ₁               ≡⟨ Eq.cong (b +_) (*-identityʳ (- b)) ⟩
    b + (- b)                   ≡⟨ +-inverseʳ b ⟩
    ₀ ∎

------------------------------------------------------------------------
-- How the a-box transforms an arbitrary q: its top becomes sform1 p q.

e-after-abox : (p1 : ℤ ₚ × ℤ ₚ) → p1 ≢ (₀ , ₀) → (q : ℤ ₚ × ℤ ₚ) → ℤ ₚ
e-after-abox (₀ , ₀)     pr q        = ⊥-elim (pr Eq.refl)
e-after-abox (₀ , ₁₊ b') pr (qa , qb) = qb * (((₁₊ b') , λ ()) ⁻¹) .proj₁
e-after-abox (₁₊ a' , b) pr (qa , qb) = qa * (((₁₊ a') , λ ()) ⁻¹) .proj₁

lemma-abox-X : ∀ (p1 : ℤ ₚ × ℤ ₚ) (pr : p1 ≢ (₀ , ₀)) (q : Pauli1) (t : Pauli n) →
  act [ (p1 , pr) ]ᵃ (q ∷ t) ≡ (sform1 p1 q , e-after-abox p1 pr q) ∷ t
lemma-abox-X (₀ , ₀)     pr q        t = ⊥-elim (pr Eq.refl)
lemma-abox-X (₀ , ₁₊ b') pr (qa , qb) t = begin
  act (M bb) ((qa , qb) ∷ t)
    ≡⟨ act-M bb qa qb t ⟩
  (qa * (bb ⁻¹) .proj₁ , qb * (bb .proj₁)) ∷ t
    ≡⟨ Eq.cong (λ z → (qa * z , qb * (bb .proj₁)) ∷ t) (inv-involutive (₁₊ b' , λ ())) ⟩
  (qa * (₁₊ b') , qb * (bb .proj₁)) ∷ t
    ≡⟨ Eq.cong (λ z → (z , qb * (bb .proj₁)) ∷ t) (Eq.sym sform-eq) ⟩
  (sform1 (₀ , ₁₊ b') (qa , qb) , qb * (bb .proj₁)) ∷ t ∎
  where
  open ≡-Reasoning
  bb = (₁₊ b' , λ ()) ⁻¹
  sform-eq : sform1 (₀ , ₁₊ b') (qa , qb) ≡ qa * (₁₊ b')
  sform-eq = Eq.trans (Eq.cong (_+ qa * (₁₊ b')) (Eq.trans (Eq.cong (_* qb) -0#≈0#) (*-zeroˡ qb)))
                      (+-identityˡ (qa * (₁₊ b')))
lemma-abox-X (₁₊ a' , b) pr (qa , qb) t = begin
  act (M aa • (H • S^ (- b * x))) ((qa , qb) ∷ t)
    ≡⟨ Eq.cong (act (M aa)) (act-HS^ (- b * x) qa qb t) ⟩
  act (M aa) ((- (qb + qa * (- b * x)) , qa) ∷ t)
    ≡⟨ act-M aa (- (qb + qa * (- b * x))) qa t ⟩
  ((- (qb + qa * (- b * x))) * (aa ⁻¹) .proj₁ , qa * (aa .proj₁)) ∷ t
    ≡⟨ Eq.cong (λ z → ((- (qb + qa * (- b * x))) * z , qa * (aa .proj₁)) ∷ t) (inv-involutive (₁₊ a' , λ ())) ⟩
  ((- (qb + qa * (- b * x))) * (₁₊ a') , qa * (aa .proj₁)) ∷ t
    ≡⟨ Eq.cong (λ z → (z , qa * (aa .proj₁)) ∷ t) first-eq ⟩
  (sform1 (₁₊ a' , b) (qa , qb) , qa * (aa .proj₁)) ∷ t ∎
  where
  open ≡-Reasoning
  aa = (₁₊ a' , λ ()) ⁻¹
  x  = ((₁₊ a' , λ ()) ⁻¹) .proj₁
  reduce-c : qa * (- b * x) * (₁₊ a') ≡ - (qa * b)
  reduce-c = begin
    qa * (- b * x) * (₁₊ a')       ≡⟨ *-assoc qa (- b * x) (₁₊ a') ⟩
    qa * ((- b * x) * (₁₊ a'))     ≡⟨ Eq.cong (qa *_) (*-assoc (- b) x (₁₊ a')) ⟩
    qa * ((- b) * (x * (₁₊ a')))   ≡⟨ Eq.cong (λ z → qa * ((- b) * z)) (Eq.trans (*-comm x (₁₊ a')) (lemma-⁻¹ʳ (₁₊ a') {{nztoℕ {y = ₁₊ a'} {neq0 = λ ()}}})) ⟩
    qa * ((- b) * ₁)               ≡⟨ Eq.cong (λ z → qa * z) (*-identityʳ (- b)) ⟩
    qa * (- b)                     ≡⟨ Eq.trans (*-comm qa (- b)) (Eq.trans (Eq.sym (-‿distribˡ-* b qa)) (Eq.cong -_ (*-comm b qa))) ⟩
    - (qa * b) ∎
  first-eq : (- (qb + qa * (- b * x))) * (₁₊ a') ≡ sform1 (₁₊ a' , b) (qa , qb)
  first-eq = begin
    (- (qb + qa * (- b * x))) * (₁₊ a')
      ≡⟨ Eq.sym (-‿distribˡ-* (qb + qa * (- b * x)) (₁₊ a')) ⟩
    - ((qb + qa * (- b * x)) * (₁₊ a'))
      ≡⟨ Eq.cong -_ (*-distribʳ-+ (₁₊ a') qb (qa * (- b * x))) ⟩
    - (qb * (₁₊ a') + qa * (- b * x) * (₁₊ a'))
      ≡⟨ Eq.cong (λ z → - (qb * (₁₊ a') + z)) reduce-c ⟩
    - (qb * (₁₊ a') + (- (qa * b)))
      ≡⟨ Eq.trans (Eq.sym (-‿+-comm (qb * (₁₊ a')) (- (qa * b)))) (Eq.cong (- (qb * (₁₊ a')) +_) (-‿involutive (qa * b))) ⟩
    - (qb * (₁₊ a')) + qa * b
      ≡⟨ Eq.cong (_+ qa * b) (Eq.trans (Eq.cong -_ (*-comm qb (₁₊ a'))) (-‿distribˡ-* (₁₊ a') qb)) ⟩
    (- (₁₊ a')) * qb + qa * b ∎
