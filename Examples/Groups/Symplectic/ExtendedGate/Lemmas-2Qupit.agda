{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq



open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
import Data.Nat as Nat


open import Word.Base as WB hiding (wfoldl)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full



open import Data.Fin using (toℕ)
import Data.Nat.Properties as NP
open import Data.Nat.Primality



module Examples.Groups.Symplectic.ExtendedGate.Lemmas-2Qupit (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where





open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime

module Lemmas-2Q (n : ℕ) where

  open Symplectic-Derived-Gen
  open import Zp.ModularArithmetic

  open PB ((₂₊ n) QRel,_===_) hiding (_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Pattern-Assoc
  open import Data.Nat.DivMod
  open import Data.Fin.Properties

  lemma-CZ^k-% : ∀ k -> CZ ^ k ≈ CZ ^ (k % p)
  lemma-CZ^k-% k = begin
    CZ ^ k ≡⟨ Eq.cong (CZ ^_) (m≡m%n+[m/n]*n k p) ⟩
    CZ ^ (k Nat.% p Nat.+ k Nat./ p Nat.* p) ≈⟨ ^-+ CZ (k Nat.% p) (k Nat./ p Nat.* p) ⟩
    CZ ^ (k Nat.% p) • CZ ^ (k Nat./ p Nat.* p) ≈⟨ (cright refl' (Eq.cong (CZ ^_) (NP.*-comm (k Nat./ p) p))) ⟩
    CZ ^ (k Nat.% p) • CZ ^ (p Nat.* (k Nat./ p)) ≈⟨ sym (cright ^^ CZ p (k Nat./ p)) ⟩
    CZ ^ (k Nat.% p) • (CZ ^ p) ^ (k Nat./ p) ≈⟨ (cright ^-cong (CZ ^ p) ε (k Nat./ p) (axiom (srel order-CZ))) ⟩
    CZ ^ (k Nat.% p) • (ε) ^ (k Nat./ p) ≈⟨ (cright ε^k=ε (k Nat./ p)) ⟩
    CZ ^ (k Nat.% p) • ε ≈⟨ right-unit ⟩
    CZ ^ (k % p) ∎
    where
    open SR word-setoid

  derived-M↑CZ : ∀ x k -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) ↑ • CZ ^ k ≈ CZ ^ (k Nat.* toℕ (x)) • M (x , nz) ↑
  derived-M↑CZ x k@0 nz = trans right-unit (sym left-unit)
  derived-M↑CZ x k@1 nz = begin  
    M (x , nz) ↑ • CZ ^ k ≈⟨ refl ⟩
    M (x , nz) ↑ • CZ ≈⟨ axiom (srel (semi-M↑CZ (x , nz))) ⟩
    CZ^ (x) • M (x , nz) ↑ ≈⟨ cong (axiom (srel (derived-CZ (x)))) refl ⟩
    CZ ^ toℕ (x) • M (x , nz) ↑ ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (Eq.sym ( NP.*-identityˡ (toℕ (x)))))) ⟩
    CZ ^ (k Nat.* toℕ (x)) • M (x , nz) ↑ ∎
    where
    open SR word-setoid
  derived-M↑CZ x k@(₂₊ k') nz = begin  
    M (x , nz) ↑ • CZ ^ k ≈⟨ refl ⟩
    M (x , nz) ↑ • CZ • CZ ^ ₁₊ k' ≈⟨ sym assoc ⟩
    (M (x , nz) ↑ • CZ) • CZ ^ ₁₊ k' ≈⟨ (cleft derived-M↑CZ x 1 nz) ⟩
    (CZ ^ (1 Nat.* toℕ (x)) • M (x , nz) ↑) • CZ ^ ₁₊ k' ≈⟨ assoc ⟩
    CZ ^ (1 Nat.* toℕ (x)) • M (x , nz) ↑ • CZ ^ ₁₊ k' ≈⟨ (cright derived-M↑CZ x (₁₊ k') nz) ⟩
    CZ ^ (1 Nat.* toℕ (x)) • CZ ^ (₁₊ k' Nat.* toℕ (x)) • M (x , nz) ↑ ≈⟨ sym assoc ⟩
    (CZ ^ (1 Nat.* toℕ (x)) • CZ ^ (₁₊ k' Nat.* toℕ (x))) • M (x , nz) ↑ ≈⟨ (cleft sym (^-+ CZ ((1 Nat.* toℕ (x))) ((₁₊ k' Nat.* toℕ (x))))) ⟩
    (CZ ^ ((1 Nat.* toℕ (x)) Nat.+ (₁₊ k' Nat.* toℕ (x)))) • M (x , nz) ↑ ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ (x)) ₁ (₁₊ k'))))) ⟩
    CZ ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ (x) ) • M (x , nz) ↑ ≈⟨ refl ⟩
    CZ ^ (k Nat.* toℕ (x)) • M (x , nz) ↑ ∎
    where
    open SR word-setoid

  lemma-M↑CZ^k : ∀ x k -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) ↑ • CZ^ k ≈ CZ^ (k * (x)) • M (x , nz) ↑
  lemma-M↑CZ^k x k nz = begin 
    M (x , nz) ↑ • CZ^ k ≈⟨ cong refl (axiom (srel (derived-CZ k))) ⟩
    M (x , nz) ↑ • CZ ^ toℕ k ≈⟨ derived-M↑CZ x (toℕ k) nz ⟩
    CZ ^ (toℕ k Nat.* toℕ (x)) • M (x , nz) ↑ ≈⟨ (cleft lemma-CZ^k-% (toℕ k Nat.* toℕ (x))) ⟩
    CZ ^ ((toℕ k Nat.* toℕ (x)) % p) • M (x , nz) ↑ ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (lemma-toℕ-% k (x)))) ⟩
    CZ ^ toℕ (k * (x)) • M (x , nz) ↑ ≈⟨ cong (sym (axiom (srel (derived-CZ (k * (x)))))) refl ⟩
    CZ^ (k * (x)) • M (x , nz) ↑ ∎
    where
    open SR word-setoid
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹


  derived-M↓CZ : ∀ x k -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) ↓ • CZ ^ k ≈ CZ ^ (k Nat.* toℕ (x)) • M (x , nz) ↓
  derived-M↓CZ x k@0 nz = trans right-unit (sym left-unit)
  derived-M↓CZ x k@1 nz = begin  
    M (x , nz) ↓ • CZ ^ k ≈⟨ refl ⟩
    M (x , nz) ↓ • CZ ≈⟨ axiom (srel (semi-M↓CZ (x , nz))) ⟩
    CZ^ (x) • M (x , nz) ↓ ≈⟨ cong (axiom (srel (derived-CZ (x)))) refl ⟩
    CZ ^ toℕ (x) • M (x , nz) ↓ ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (Eq.sym ( NP.*-identityˡ (toℕ (x)))))) ⟩
    CZ ^ (k Nat.* toℕ (x)) • M (x , nz) ↓ ∎
    where
    open SR word-setoid
  derived-M↓CZ x k@(₂₊ k') nz = begin  
    M (x , nz) ↓ • CZ ^ k ≈⟨ refl ⟩
    M (x , nz) ↓ • CZ • CZ ^ ₁₊ k' ≈⟨ sym assoc ⟩
    (M (x , nz) ↓ • CZ) • CZ ^ ₁₊ k' ≈⟨ (cleft derived-M↓CZ x 1 nz) ⟩
    (CZ ^ (1 Nat.* toℕ (x)) • M (x , nz) ↓) • CZ ^ ₁₊ k' ≈⟨ assoc ⟩
    CZ ^ (1 Nat.* toℕ (x)) • M (x , nz) ↓ • CZ ^ ₁₊ k' ≈⟨ (cright derived-M↓CZ x (₁₊ k') nz) ⟩
    CZ ^ (1 Nat.* toℕ (x)) • CZ ^ (₁₊ k' Nat.* toℕ (x)) • M (x , nz) ↓ ≈⟨ sym assoc ⟩
    (CZ ^ (1 Nat.* toℕ (x)) • CZ ^ (₁₊ k' Nat.* toℕ (x))) • M (x , nz) ↓ ≈⟨ (cleft sym (^-+ CZ ((1 Nat.* toℕ (x))) ((₁₊ k' Nat.* toℕ (x))))) ⟩
    (CZ ^ ((1 Nat.* toℕ (x)) Nat.+ (₁₊ k' Nat.* toℕ (x)))) • M (x , nz) ↓ ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ (x)) ₁ (₁₊ k'))))) ⟩
    CZ ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ (x) ) • M (x , nz) ↓ ≈⟨ refl ⟩
    CZ ^ (k Nat.* toℕ (x)) • M (x , nz) ↓ ∎
    where
    open SR word-setoid

  lemma-M↓CZ^k : ∀ x k -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) ↓ • CZ^ k ≈ CZ^ (k * (x)) • M (x , nz) ↓
  lemma-M↓CZ^k x k nz = begin 
    M (x , nz) ↓ • CZ^ k ≈⟨ cong refl (axiom (srel (derived-CZ k))) ⟩
    M (x , nz) ↓ • CZ ^ toℕ k ≈⟨ derived-M↓CZ x (toℕ k) nz ⟩
    CZ ^ (toℕ k Nat.* toℕ (x)) • M (x , nz) ↓ ≈⟨ (cleft lemma-CZ^k-% (toℕ k Nat.* toℕ (x))) ⟩
    CZ ^ ((toℕ k Nat.* toℕ (x)) % p) • M (x , nz) ↓ ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (lemma-toℕ-% k (x)))) ⟩
    CZ ^ toℕ (k * (x)) • M (x , nz) ↓ ≈⟨ cong (sym (axiom (srel (derived-CZ (k * (x)))))) refl ⟩
    CZ^ (k * (x)) • M (x , nz) ↓ ∎
    where
    open SR word-setoid
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹


  lemma-semi-CZ-HH↓ : 

    CZ • H ↓ ^ 2 ≈ H ↓ ^ 2 • CZ^ ₋₁
    
  lemma-semi-CZ-HH↓ = begin
    CZ • H ↓ ^ 2 ≈⟨ (cright lemma-HH-M-1) ⟩
    CZ^ ₁ • M -'₁ ↓ ≡⟨ Eq.cong (\ xx -> CZ^ xx • M -'₁ ↓) (Eq.sym aux-₋₁*₋₁=₁) ⟩
    CZ^ (₋₁ * ₋₁) • M -'₁ ↓ ≡⟨ Eq.cong (\ xx -> CZ^ (₋₁ * xx) • M -'₁ ↓) (Eq.sym aux-1=-1) ⟩
    CZ^ (₋₁ * -'₁ .proj₁) • M -'₁ ↓ ≈⟨ sym (lemma-M↓CZ^k (-'₁ .proj₁) ₋₁ (-'₁ .proj₂)) ⟩
    M -'₁ ↓ • CZ^ ₋₁ ≈⟨ (cleft sym lemma-HH-M-1) ⟩
    H ↓ ^ 2 • CZ^ ₋₁ ∎
    where
    open SR word-setoid
    open Lemmas0 (₁₊ n)


  lemma-semi-CZ-HH↑ : 

    CZ • H ↑ ^ 2 ≈ H ↑ ^ 2 • CZ^ ₋₁
    
  lemma-semi-CZ-HH↑ = begin
    CZ • H ↑ ^ 2 ≈⟨ (cright (lemma-cong↑ _ _ lemma-HH-M-1)) ⟩
    CZ^ ₁ • M -'₁ ↑ ≡⟨ Eq.cong (\ xx -> CZ^ xx • M -'₁ ↑) (Eq.sym aux-₋₁*₋₁=₁) ⟩
    CZ^ (₋₁ * ₋₁) • M -'₁ ↑ ≡⟨ Eq.cong (\ xx -> CZ^ (₋₁ * xx) • M -'₁ ↑) (Eq.sym aux-1=-1) ⟩
    CZ^ (₋₁ * -'₁ .proj₁) • M -'₁ ↑ ≈⟨ sym (lemma-M↑CZ^k (-'₁ .proj₁) ₋₁ (-'₁ .proj₂)) ⟩
    M -'₁ ↑ • CZ^ ₋₁ ≈⟨ (cleft sym (lemma-cong↑ _ _ lemma-HH-M-1)) ⟩
    H ↑ ^ 2 • CZ^ ₋₁ ∎
    where
    open SR word-setoid
    open Lemmas0 (n)

  open import Algebra.Properties.Ring (+-*-ring p-2)


  lemma-semi-HH↑-CZ^k : ∀ k ->

    HH ↑ • CZ^ k ≈ CZ^ (- k) • HH ↑
    
  lemma-semi-HH↑-CZ^k k = begin
    HH ↑ • CZ^ k ≈⟨ (cleft lemma-cong↑ _ _ lemma-HH-M-1) ⟩
    M -'₁ ↑ • CZ^ k ≈⟨ lemma-M↑CZ^k (- ₁) k (-'₁ .proj₂) ⟩
    CZ^ (k * - ₁) • M -'₁ ↑ ≈⟨ cong (refl' (Eq.cong CZ^ (*-comm k (- ₁)))) (sym (lemma-cong↑ _ _ lemma-HH-M-1)) ⟩
    CZ^ (- ₁ * k) • HH ↑ ≈⟨ cleft (refl' (Eq.cong CZ^ (-1*x≈-x k)))  ⟩
    CZ^ (- k) • HH ↑ ∎
    where
    open SR word-setoid
    open Lemmas0 (n)
    
  lemma-semi-HH↓-CZ^k : ∀ k ->

    HH ↓ • CZ^ k ≈ CZ^ (- k) • HH ↓
    
  lemma-semi-HH↓-CZ^k k = begin
    HH ↓ • CZ^ k ≈⟨ (cleft L1.lemma-HH-M-1) ⟩
    M -'₁ ↓ • CZ^ k ≈⟨ lemma-M↓CZ^k (- ₁) k (-'₁ .proj₂) ⟩
    CZ^ (k * - ₁) • M -'₁ ↓ ≈⟨ cong (refl' (Eq.cong CZ^ (*-comm k (- ₁)))) (sym (L1.lemma-HH-M-1)) ⟩
    CZ^ (- ₁ * k) • HH ↓ ≈⟨ cleft (refl' (Eq.cong CZ^ (-1*x≈-x k)))  ⟩
    CZ^ (- k) • HH ↓ ∎
    where
    open SR word-setoid
    open Lemmas0 (n)
    module L1 = Lemmas0 (₁₊ n)
    
