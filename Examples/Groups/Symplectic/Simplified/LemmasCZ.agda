------------------------------------------------------------------------
-- Presentations of groups
--
-- Derived rules for CZ
--
-- Conjugation of CZ by the M family, on either wire: the CZ analogues
-- of the S lemmas in Lemmas, ending in semi-M↓CZ and semi-M↑CZ, which
-- are exactly the two axioms Iso has to discharge.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --termination-depth=20 #-}

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning ; _≢_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Nat.DivMod
open import Agda.Builtin.Nat using ()
import Data.Nat as Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Bool
open import Data.List hiding ([_])


open import Data.Maybe
open import Data.Sum using ([_,_])
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
import Circuit.Base
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full
open import Presentation.Tactic.Rewriting

open import Presentation.Construct.Base hiding (_*_)


open import Data.Fin.Properties as FP using (toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Data.Nat.Primality
open import Data.Nat.Coprimality hiding (sym)
open import Data.Nat.GCD
open Bézout
open import Data.Empty
open import Algebra.Properties.Group
open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem

module Examples.Groups.Symplectic.Simplified.LemmasCZ
  (p-2 : ℕ)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime as NSym
open Symplectic hiding (_QRel,_===_ ; srel ; cong↑ ; comm₁ ; comm₂ ; lemma-cong↑ ; order-S ; order-H ; semi-MS ; semi-M↑CZ ; semi-M↓CZ ; order-CZ ; comm-CZ-S↓ ; comm-CZ-S↑ ; selinger-c10 ; selinger-c11 ; selinger-c12 ; selinger-c13 ; selinger-c14 ; selinger-c15)

open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
open import Examples.Groups.Symplectic.Simplified.Lemmas p-2 p-prime g* g-gen

module Lemmas2 (n : ℕ) where

  open Simplified-Relations
  open Symplectic-Sim-GroupLike

  open PB ((₂₊ n) QRel,_===_) hiding (_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Pattern-Assoc
  open import Data.Nat.DivMod
  open import Data.Fin.Properties
  module LL0 = Lemmas1 n
  module LLb0 = Lemmas1b n
  open Lemmas1 (₁₊ n)
  open Lemmas1b (₁₊ n)


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


  lemma-Mg↓CZ^k : ∀ k ->  let g⁻¹ = (g′ ⁻¹) .proj₁ in let -g⁻¹ = - g⁻¹ in
    Mg • CZ ^ k ≈ CZ ^ (k Nat.* toℕ g) • Mg
  lemma-Mg↓CZ^k k@0 = trans right-unit (sym left-unit)
  lemma-Mg↓CZ^k k@1 = begin  
    Mg • CZ ^ k ≈⟨ refl ⟩
    Mg • CZ ≈⟨ axiom (srel semi-M↓CZ) ⟩
    CZ^ g • Mg ≈⟨ refl ⟩
    CZ ^ toℕ g • Mg ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (Eq.sym ( NP.*-identityˡ (toℕ g))))) ⟩
    CZ ^ (k Nat.* toℕ g) • Mg ∎
    where
    open SR word-setoid
  lemma-Mg↓CZ^k k@(₂₊ k') = begin  
    Mg • CZ ^ k ≈⟨ refl ⟩
    Mg • CZ • CZ ^ ₁₊ k' ≈⟨ sym assoc ⟩
    (Mg • CZ) • CZ ^ ₁₊ k' ≈⟨ (cleft lemma-Mg↓CZ^k 1 ) ⟩
    (CZ ^ (1 Nat.* toℕ g) • Mg) • CZ ^ ₁₊ k' ≈⟨ assoc ⟩
    CZ ^ (1 Nat.* toℕ g) • Mg • CZ ^ ₁₊ k' ≈⟨ (cright lemma-Mg↓CZ^k (₁₊ k')) ⟩
    CZ ^ (1 Nat.* toℕ g) • CZ ^ (₁₊ k' Nat.* toℕ g) • Mg ≈⟨ sym assoc ⟩
    (CZ ^ (1 Nat.* toℕ g) • CZ ^ (₁₊ k' Nat.* toℕ g)) • Mg ≈⟨ (cleft sym (^-+ CZ ((1 Nat.* toℕ g)) ((₁₊ k' Nat.* toℕ g)))) ⟩
    (CZ ^ ((1 Nat.* toℕ g) Nat.+ (₁₊ k' Nat.* toℕ g))) • Mg ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ g) ₁ (₁₊ k'))))) ⟩
    CZ ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ g ) • Mg ≈⟨ refl ⟩
    CZ ^ (k Nat.* toℕ g) • Mg ∎
    where
    open SR word-setoid

  lemma-Mg↓CZ^k' : ∀ k -> let x⁻¹ = (g′ ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    Mg • CZ^ k ≈ CZ^ (k * g) • Mg
  lemma-Mg↓CZ^k' k = begin 
    Mg • CZ^ k ≈⟨ refl ⟩
    Mg • CZ ^ toℕ k ≈⟨ lemma-Mg↓CZ^k (toℕ k) ⟩
    CZ ^ (toℕ k Nat.* toℕ g) • Mg ≈⟨ (cleft lemma-CZ^k-% (toℕ k Nat.* toℕ g)) ⟩
    CZ ^ ((toℕ k Nat.* toℕ g) % p) • Mg ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (lemma-toℕ-% k g))) ⟩
    CZ ^ toℕ (k * g) • Mg ≈⟨ refl ⟩
    CZ^ (k * g) • Mg ∎
    where
    open SR word-setoid
    x⁻¹ = (g′ ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹

  lemma-Mg^kCZ : ∀ k -> Mg ^ k • CZ ≈ CZ^ (g ^′ k) • Mg ^ k
  lemma-Mg^kCZ k@0 = trans left-unit (sym right-unit)
  lemma-Mg^kCZ k@1 = begin
    Mg ^ k • CZ ≈⟨ axiom (srel semi-M↓CZ) ⟩
    CZ^ (g) • Mg ^ k ≈⟨ (cleft refl' (Eq.cong CZ^ (Eq.sym (lemma-x^′1=x g)))) ⟩
    CZ^ (g ^′ k) • Mg ^ k ∎
    where
    open SR word-setoid
  lemma-Mg^kCZ k@(₂₊ n) = begin
    (Mg • Mg ^ ₁₊ n) • CZ ≈⟨ assoc ⟩
    Mg • Mg ^ ₁₊ n • CZ ≈⟨ (cright lemma-Mg^kCZ (₁₊ n)) ⟩
    Mg • CZ^ (g ^′ (₁₊ n)) • Mg ^ (₁₊ n) ≈⟨ sym assoc ⟩
    (Mg • CZ^ (g ^′ (₁₊ n))) • Mg ^ (₁₊ n) ≈⟨ (cleft lemma-Mg↓CZ^k' (g ^′ (₁₊ n))) ⟩
    (CZ^ ((g ^′ (₁₊ n)) * g) • Mg) • Mg ^ (₁₊ n) ≈⟨ refl' (Eq.cong (\ xx -> (CZ^ xx • Mg) • Mg ^ (₁₊ n)) (*-comm (g ^′ (₁₊ n)) g)) ⟩
    (CZ^ (g * (g ^′ (₁₊ n))) • Mg) • Mg ^ (₁₊ n) ≈⟨ assoc ⟩
    CZ^ (g ^′ k) • Mg • Mg ^ ₁₊ n ∎
    where
    open SR word-setoid



  lemma-semi-M↓CZ : ∀ x -> let x' = x .proj₁ in let k = g-gen x .proj₁ in M x • CZ ≈ CZ^ x' • M x
  lemma-semi-M↓CZ x = begin
    M x • CZ ≈⟨ (cleft refl' (aux-M≡M x (g^ k) (eqk))) ⟩
    M (g^ k) • CZ ≈⟨ cong (sym (axiom (srel (M-power (k))))) refl ⟩
    Mg^ k • CZ ≈⟨ lemma-Mg^kCZ (toℕ k) ⟩
    CZ^ (g ^′ toℕ k) • Mg^ k ≈⟨ (cright axiom (srel (M-power (k)))) ⟩
    CZ^ (g ^′ toℕ k) • M (g^ k) ≈⟨ (cleft refl' (Eq.cong CZ^ (Eq.sym eqk))) ⟩
    CZ^ (x') • M (g^ k) ≈⟨ (cright refl' (aux-M≡M (g^ k) x (Eq.sym (eqk)))) ⟩
    CZ^ (x') • M x ∎
    where
    open SR word-setoid
    x' = x .proj₁
    k = inject₁ (g-gen x .proj₁)
    eqk : x .proj₁ ≡ (g^ k) .proj₁
    eqk = Eq.sym (lemma-log-inject x)






  lemma-Mg↑CZ^k : ∀ k ->  let g⁻¹ = (g′ ⁻¹) .proj₁ in let -g⁻¹ = - g⁻¹ in
    Mg ↑ • CZ ^ k ≈ CZ ^ (k Nat.* toℕ g) • Mg ↑
  lemma-Mg↑CZ^k k@0 = trans right-unit (sym left-unit)
  lemma-Mg↑CZ^k k@1 = begin  
    Mg ↑ • CZ ^ k ≈⟨ refl ⟩
    Mg ↑ • CZ ≈⟨ axiom (srel semi-M↑CZ) ⟩
    CZ^ g • Mg ↑ ≈⟨ refl ⟩
    CZ ^ toℕ g • Mg ↑ ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (Eq.sym ( NP.*-identityˡ (toℕ g))))) ⟩
    CZ ^ (k Nat.* toℕ g) • Mg ↑ ∎
    where
    open SR word-setoid
  lemma-Mg↑CZ^k k@(₂₊ k') = begin  
    Mg ↑ • CZ ^ k ≈⟨ refl ⟩
    Mg ↑ • CZ • CZ ^ ₁₊ k' ≈⟨ sym assoc ⟩
    (Mg ↑ • CZ) • CZ ^ ₁₊ k' ≈⟨ (cleft lemma-Mg↑CZ^k 1 ) ⟩
    (CZ ^ (1 Nat.* toℕ g) • Mg ↑) • CZ ^ ₁₊ k' ≈⟨ assoc ⟩
    CZ ^ (1 Nat.* toℕ g) • Mg ↑ • CZ ^ ₁₊ k' ≈⟨ (cright lemma-Mg↑CZ^k (₁₊ k')) ⟩
    CZ ^ (1 Nat.* toℕ g) • CZ ^ (₁₊ k' Nat.* toℕ g) • Mg ↑ ≈⟨ sym assoc ⟩
    (CZ ^ (1 Nat.* toℕ g) • CZ ^ (₁₊ k' Nat.* toℕ g)) • Mg ↑ ≈⟨ (cleft sym (^-+ CZ ((1 Nat.* toℕ g)) ((₁₊ k' Nat.* toℕ g)))) ⟩
    (CZ ^ ((1 Nat.* toℕ g) Nat.+ (₁₊ k' Nat.* toℕ g))) • Mg ↑ ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ g) ₁ (₁₊ k'))))) ⟩
    CZ ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ g ) • Mg ↑ ≈⟨ refl ⟩
    CZ ^ (k Nat.* toℕ g) • Mg ↑ ∎
    where
    open SR word-setoid

  lemma-Mg↑CZ^k' : ∀ k -> let x⁻¹ = (g′ ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    Mg ↑ • CZ^ k ≈ CZ^ (k * g) • Mg ↑
  lemma-Mg↑CZ^k' k = begin 
    Mg ↑ • CZ^ k ≈⟨ refl ⟩
    Mg ↑ • CZ ^ toℕ k ≈⟨ lemma-Mg↑CZ^k (toℕ k) ⟩
    CZ ^ (toℕ k Nat.* toℕ g) • Mg ↑ ≈⟨ (cleft lemma-CZ^k-% (toℕ k Nat.* toℕ g)) ⟩
    CZ ^ ((toℕ k Nat.* toℕ g) % p) • Mg ↑ ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (lemma-toℕ-% k g))) ⟩
    CZ ^ toℕ (k * g) • Mg ↑ ≈⟨ refl ⟩
    CZ^ (k * g) • Mg ↑ ∎
    where
    open SR word-setoid
    x⁻¹ = (g′ ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹

  lemma-Mg^k↑CZ : ∀ k -> Mg ↑ ^ k • CZ ≈ CZ^ (g ^′ k) • Mg ↑ ^ k
  lemma-Mg^k↑CZ k@0 = trans left-unit (sym right-unit)
  lemma-Mg^k↑CZ k@1 = begin
    Mg ↑ ^ k • CZ ≈⟨ axiom (srel semi-M↑CZ) ⟩
    CZ^ (g) • Mg ↑ ^ k ≈⟨ (cleft refl' (Eq.cong CZ^ (Eq.sym (lemma-x^′1=x g)))) ⟩
    CZ^ (g ^′ k) • Mg ↑ ^ k ∎
    where
    open SR word-setoid
  lemma-Mg^k↑CZ k@(₂₊ n) = begin
    (Mg ↑ • Mg ↑ ^ ₁₊ n) • CZ ≈⟨ assoc ⟩
    Mg ↑ • Mg ↑ ^ ₁₊ n • CZ ≈⟨ (cright lemma-Mg^k↑CZ (₁₊ n)) ⟩
    Mg ↑ • CZ^ (g ^′ (₁₊ n)) • Mg ↑ ^ (₁₊ n) ≈⟨ sym assoc ⟩
    (Mg ↑ • CZ^ (g ^′ (₁₊ n))) • Mg ↑ ^ (₁₊ n) ≈⟨ (cleft lemma-Mg↑CZ^k' (g ^′ (₁₊ n))) ⟩
    (CZ^ ((g ^′ (₁₊ n)) * g) • Mg ↑) • Mg ↑ ^ (₁₊ n) ≈⟨ refl' (Eq.cong (\ xx -> (CZ^ xx • Mg ↑) • Mg ↑ ^ (₁₊ n)) (*-comm (g ^′ (₁₊ n)) g)) ⟩
    (CZ^ (g * (g ^′ (₁₊ n))) • Mg ↑) • Mg ↑ ^ (₁₊ n) ≈⟨ assoc ⟩
    CZ^ (g ^′ k) • Mg ↑ • Mg ↑ ^ ₁₊ n ∎
    where
    open SR word-setoid



  lemma-semi-M↑CZ : ∀ x -> let x' = x .proj₁ in let k = g-gen x .proj₁ in M x ↑ • CZ ≈ CZ^ x' • M x ↑ 
  lemma-semi-M↑CZ x = begin
    M x ↑ • CZ ≈⟨ (cleft (lemma-cong↑ _ _ ((aux-MM (x .proj₂) (((g^ k) .proj₂))  ( (eqk)))))) ⟩
    M (g^ k) ↑ • CZ ≈⟨ cong (sym (axiom (cong↑ (srel (M-power (k)))))) refl ⟩
    (Mg ^ toℕ k) ↑ • CZ ≈⟨ (cleft refl' (lemma-↑^ (toℕ k) Mg)) ⟩
    Mg ↑ ^ toℕ k • CZ ≈⟨ lemma-Mg^k↑CZ (toℕ k) ⟩
    CZ^ (g ^′ toℕ k) • Mg ↑ ^ toℕ k ≈⟨ (cright sym (refl' (lemma-↑^ (toℕ k) Mg))) ⟩
    CZ^ (g ^′ toℕ k) • (Mg ^ toℕ k) ↑ ≈⟨ (cright axiom (cong↑ (srel (M-power (k))))) ⟩
    CZ^ (g ^′ toℕ k) • M (g^ k) ↑ ≈⟨ (cleft refl' (Eq.cong CZ^ (Eq.sym eqk))) ⟩
    CZ^ (x') • M (g^ k) ↑ ≈⟨ (cright (lemma-cong↑ _ _ ((aux-MM (((g^ k) .proj₂)) (x .proj₂) (Eq.sym (eqk)))))) ⟩
    CZ^ (x') • M x ↑ ∎
    where
    open Lemmas-Sim
    open SR word-setoid
    x' = x .proj₁
    k = inject₁ (g-gen x .proj₁)
    eqk : x .proj₁ ≡ (g^ k) .proj₁
    eqk = Eq.sym (lemma-log-inject x)
