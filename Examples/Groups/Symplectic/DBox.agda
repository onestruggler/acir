------------------------------------------------------------------------
-- Presentations of groups
--
-- The D-box actions used by the width recursion of Theorem-LM.  The
-- D-box [ q ]ᵈ (a two-qupit box, Section.[_]ᵈ) clears the top two wires:
--
--   lemma-dbox-IZ :  act [ q ]ᵈ (pI ∷ pZ ∷ t) ≡ pZ ∷ pI ∷ t
--   lemma-dbox    :  act [ q ]ᵈ (q  ∷ pX ∷ t) ≡ pX ∷ pI ∷ t
--
-- Both hold for either shape of q, built from act-Ex / act-CZ^ /
-- act-S^ / act-H (Examples.Groups.Symplectic.BoxAction).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.DBox (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_,_ ; proj₁)
open import Data.Vec using (_∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; module ≡-Reasoning)

open import Notations
open import Word.Base using (_•_)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime using (Pauli ; pZ ; pX ; pI)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic using (H ; S^ ; CZ^ ; Ex)

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime using (D ; [_]ᵈ)

open import Examples.Groups.Symplectic.BoxAction p-2 p-prime
  using (act ; act-S^ ; act-H ; act-CZ^ ; act-Ex)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- act [ q ]ᵈ (pI ∷ pZ ∷ t) = pZ ∷ pI ∷ t   (q is inert on (I,Z))

lemma-dbox-IZ : ∀ (q : D) (t : Pauli n) → act [ q ]ᵈ (pI ∷ pZ ∷ t) ≡ pZ ∷ pI ∷ t
lemma-dbox-IZ (₀ , b) t = begin
  act (Ex • CZ^ (- b)) (pI ∷ pZ ∷ t)
    ≡⟨ Eq.cong (act Ex) (act-CZ^ (- b) ₀ ₀ ₀ ₁ t) ⟩
  act Ex ((₀ , ₀ + ₀ * (- b)) ∷ (₀ , ₁ + ₀ * (- b)) ∷ t)
    ≡⟨ Eq.cong₂ (λ z w → act Ex ((₀ , z) ∷ (₀ , w) ∷ t))
         (Eq.trans (Eq.cong (₀ +_) (*-zeroˡ (- b))) (+-identityʳ ₀))
         (Eq.trans (Eq.cong (₁ +_) (*-zeroˡ (- b))) (+-identityʳ ₁)) ⟩
  act Ex ((₀ , ₀) ∷ (₀ , ₁) ∷ t)
    ≡⟨ act-Ex ₀ ₀ ₀ ₁ t ⟩
  pZ ∷ pI ∷ t ∎
  where open ≡-Reasoning
lemma-dbox-IZ (₁₊ c' , d) t = begin
  act (Ex • CZ^ (- (₁₊ c')) • H • S^ (- d * x)) (pI ∷ pZ ∷ t)
    ≡⟨ Eq.cong (λ z → act (Ex • CZ^ (- (₁₊ c'))) (act H z)) (act-S^ (- d * x) ₀ ₀ ((₀ , ₁) ∷ t)) ⟩
  act (Ex • CZ^ (- (₁₊ c'))) (act H ((₀ , ₀ + ₀ * (- d * x)) ∷ (₀ , ₁) ∷ t))
    ≡⟨ Eq.cong (λ z → act (Ex • CZ^ (- (₁₊ c'))) (act H ((₀ , z) ∷ (₀ , ₁) ∷ t)))
         (Eq.trans (Eq.cong (₀ +_) (*-zeroˡ (- d * x))) (+-identityʳ ₀)) ⟩
  act (Ex • CZ^ (- (₁₊ c'))) (act H ((₀ , ₀) ∷ (₀ , ₁) ∷ t))
    ≡⟨ Eq.cong (act Ex) (act-CZ^ (- (₁₊ c')) (- ₀) ₀ ₀ ₁ t) ⟩
  act Ex ((- ₀ , ₀ + ₀ * (- (₁₊ c'))) ∷ (₀ , ₁ + (- ₀) * (- (₁₊ c'))) ∷ t)
    ≡⟨ Eq.cong₂ (λ z w → act Ex ((z , ₀ + ₀ * (- (₁₊ c'))) ∷ (₀ , w) ∷ t))
         -0#≈0# (Eq.trans (Eq.cong (λ u → ₁ + u * (- (₁₊ c'))) -0#≈0#) (Eq.trans (Eq.cong (₁ +_) (*-zeroˡ (- (₁₊ c')))) (+-identityʳ ₁))) ⟩
  act Ex ((₀ , ₀ + ₀ * (- (₁₊ c'))) ∷ (₀ , ₁) ∷ t)
    ≡⟨ Eq.cong (λ z → act Ex ((₀ , z) ∷ (₀ , ₁) ∷ t))
         (Eq.trans (Eq.cong (₀ +_) (*-zeroˡ (- (₁₊ c')))) (+-identityʳ ₀)) ⟩
  act Ex ((₀ , ₀) ∷ (₀ , ₁) ∷ t)
    ≡⟨ act-Ex ₀ ₀ ₀ ₁ t ⟩
  pZ ∷ pI ∷ t ∎
  where
  open ≡-Reasoning
  x = ((₁₊ c' , λ ()) ⁻¹) .proj₁

------------------------------------------------------------------------
-- act [ q ]ᵈ (q ∷ pX ∷ t) = pX ∷ pI ∷ t   (q clears the top wire)

lemma-dbox : ∀ (q : D) (t : Pauli n) → act [ q ]ᵈ (q ∷ pX ∷ t) ≡ pX ∷ pI ∷ t
lemma-dbox (₀ , b) t = begin
  act (Ex • CZ^ (- b)) ((₀ , b) ∷ pX ∷ t)
    ≡⟨ Eq.cong (act Ex) (act-CZ^ (- b) ₀ b ₁ ₀ t) ⟩
  act Ex ((₀ , b + ₁ * (- b)) ∷ (₁ , ₀ + ₀ * (- b)) ∷ t)
    ≡⟨ Eq.cong₂ (λ z w → act Ex ((₀ , z) ∷ (₁ , w) ∷ t))
         (Eq.trans (Eq.cong (b +_) (*-identityˡ (- b))) (+-inverseʳ b))
         (Eq.trans (Eq.cong (₀ +_) (*-zeroˡ (- b))) (+-identityʳ ₀)) ⟩
  act Ex ((₀ , ₀) ∷ (₁ , ₀) ∷ t)
    ≡⟨ act-Ex ₀ ₀ ₁ ₀ t ⟩
  pX ∷ pI ∷ t ∎
  where open ≡-Reasoning
lemma-dbox (₁₊ c' , d) t = begin
  act (Ex • CZ^ (- (₁₊ c')) • H • S^ (- d * x)) ((₁₊ c' , d) ∷ pX ∷ t)
    ≡⟨ Eq.cong (λ z → act (Ex • CZ^ (- (₁₊ c'))) (act H z)) (act-S^ (- d * x) (₁₊ c') d ((₁ , ₀) ∷ t)) ⟩
  act (Ex • CZ^ (- (₁₊ c'))) (act H ((₁₊ c' , d + (₁₊ c') * (- d * x)) ∷ (₁ , ₀) ∷ t))
    ≡⟨ Eq.cong (λ z → act (Ex • CZ^ (- (₁₊ c'))) (act H ((₁₊ c' , z) ∷ (₁ , ₀) ∷ t))) top=0 ⟩
  act (Ex • CZ^ (- (₁₊ c'))) (act H ((₁₊ c' , ₀) ∷ (₁ , ₀) ∷ t))
    ≡⟨ Eq.cong (act Ex) (act-CZ^ (- (₁₊ c')) (- ₀) (₁₊ c') ₁ ₀ t) ⟩
  act Ex ((- ₀ , (₁₊ c') + ₁ * (- (₁₊ c'))) ∷ (₁ , ₀ + (- ₀) * (- (₁₊ c'))) ∷ t)
    ≡⟨ Eq.cong₂ (λ z w → act Ex ((z , (₁₊ c') + ₁ * (- (₁₊ c'))) ∷ (₁ , w) ∷ t))
         -0#≈0# (Eq.trans (Eq.cong (λ u → ₀ + u * (- (₁₊ c'))) -0#≈0#) (Eq.trans (Eq.cong (₀ +_) (*-zeroˡ (- (₁₊ c')))) (+-identityʳ ₀))) ⟩
  act Ex ((₀ , (₁₊ c') + ₁ * (- (₁₊ c'))) ∷ (₁ , ₀) ∷ t)
    ≡⟨ Eq.cong (λ z → act Ex ((₀ , z) ∷ (₁ , ₀) ∷ t))
         (Eq.trans (Eq.cong ((₁₊ c') +_) (*-identityˡ (- (₁₊ c')))) (+-inverseʳ (₁₊ c'))) ⟩
  act Ex ((₀ , ₀) ∷ (₁ , ₀) ∷ t)
    ≡⟨ act-Ex ₀ ₀ ₁ ₀ t ⟩
  pX ∷ pI ∷ t ∎
  where
  open ≡-Reasoning
  x = ((₁₊ c' , λ ()) ⁻¹) .proj₁
  -- d + (₁₊c')·(-d·x) = d + (-d)·((₁₊c')·x) = d + (-d) = 0.
  top=0 : d + (₁₊ c') * (- d * x) ≡ ₀
  top=0 = begin
    d + (₁₊ c') * (- d * x)     ≡⟨ Eq.cong (d +_) (Eq.sym (*-assoc (₁₊ c') (- d) x)) ⟩
    d + (₁₊ c') * (- d) * x     ≡⟨ Eq.cong (λ z → d + z * x) (*-comm (₁₊ c') (- d)) ⟩
    d + (- d) * (₁₊ c') * x     ≡⟨ Eq.cong (d +_) (*-assoc (- d) (₁₊ c') x) ⟩
    d + (- d) * ((₁₊ c') * x)   ≡⟨ Eq.cong (λ z → d + (- d) * z) (lemma-⁻¹ʳ (₁₊ c') {{nztoℕ {y = ₁₊ c'} {neq0 = λ ()}}}) ⟩
    d + (- d) * ₁               ≡⟨ Eq.cong (d +_) (*-identityʳ (- d)) ⟩
    d + (- d)                   ≡⟨ +-inverseʳ d ⟩
    ₀ ∎
