{-# OPTIONS --cubical-compatible --safe #-}
--{-# OPTIONS --termination-depth=2 #-}

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq


open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_,_ ; proj₁)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe
open import Data.Sum using ([_,_] ; [_,_]′)
open import Data.Unit using (tt)

open import Word.Base as WB hiding (wfoldl)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)


open import Data.Fin using (toℕ)
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_])
open import Data.Nat.Primality



module Examples.Groups.Symplectic.Lemmas.Duality (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where





open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.NF2-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Cosets p-2 p-prime
open Lemmas-2Q 0
open Symplectic
open import Examples.Groups.Symplectic.ExtendedGate.NF1-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3 p-2 p-prime

open import Examples.Groups.Symplectic.Lemmas.Lemma-Comm p-2 p-prime 0
open import Examples.Groups.Symplectic.Lemmas.Lemma-Postfix p-2 p-prime
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
module L0 = Lemmas0 0

open LM2
open import Examples.Groups.Symplectic.Lemmas.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()

private
  n : ℕ
  n = 0

open Symplectic
open Symplectic-GroupLike

open import Data.Nat.DivMod
open import Data.Fin.Properties
open Duality
open import Algebra.Properties.Ring (+-*-ring p-2)

aux-dual-M : ∀ m -> dual (M m) ≡ M m ↑ 
aux-dual-M m@x' = begin
  dual (M m) ≡⟨ auto ⟩
  dual (S^ x • H • S^ x⁻¹ • H • S^ x • H) ≡⟨ Eq.cong₂ (\ xx yy -> xx • dual H • yy • dual (H • S^ x • H)) (aux-dual-S^k (toℕ (m .proj₁))) (aux-dual-S^k (toℕ x⁻¹)) ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • dual (H • S^ x • H) ≡⟨ Eq.cong (\ xx -> S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • dual H • xx • dual H) (aux-dual-S^k (toℕ x)) ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • (H ↑ • S^ x ↑ • H ↑) ≡⟨ auto ⟩
  M m ↑ ∎
  where
  open ≡-Reasoning
  x = x' .proj₁
  x⁻¹ = ((x' ⁻¹) .proj₁ )  


aux-dual-C : ∀ c -> dual ⟦ c ⟧ₕₛ ≡ ⟦ c ⟧ₕₛ ↑ 
aux-dual-C c@ε = begin
  dual ⟦ c ⟧ₕₛ ≡⟨ auto ⟩
  ⟦ c ⟧ₕₛ ↑ ∎
  where
  open ≡-Reasoning
aux-dual-C c@(HS^ k) = begin
  dual ⟦ c ⟧ₕₛ ≡⟨ Eq.cong (\ xx -> dual H • xx) (aux-dual-S^k (toℕ k)) ⟩
  ⟦ c ⟧ₕₛ ↑ ∎
  where
  open ≡-Reasoning

aux-dual-MC : ∀ mc -> dual ⟦ mc ⟧ₘ₊ ≡ ⟦ mc ⟧ₘ₊ ↑ 
aux-dual-MC mc@(m , c) = begin
  dual ⟦ mc ⟧ₘ₊ ≡⟨ Eq.cong₂ _•_ (aux-dual-M m) (aux-dual-C c) ⟩
  ⟦ mc ⟧ₘ₊ ↑ ∎
  where
  open ≡-Reasoning

aux-dual-M↑ : ∀ m -> dual (⟦ m ⟧ₘ ↑) ≡ ⟦ m ⟧ₘ
aux-dual-M↑ m = begin
  dual (⟦ m ⟧ₘ ↑) ≡⟨ Eq.cong dual (Eq.sym (aux-dual-M m)) ⟩
  dual (dual ⟦ m ⟧ₘ) ≡⟨ Eq.sym (lemma-double-dual ⟦ m ⟧ₘ) ⟩
  ⟦ m ⟧ₘ ∎
  where
  open ≡-Reasoning

aux-dual-MC↑ : ∀ mc -> dual (⟦ mc ⟧ₘ₊ ↑) ≡ ⟦ mc ⟧ₘ₊
aux-dual-MC↑ mc = begin
  dual (⟦ mc ⟧ₘ₊ ↑) ≡⟨ Eq.cong dual (Eq.sym (aux-dual-MC mc)) ⟩
  dual (dual ⟦ mc ⟧ₘ₊) ≡⟨ Eq.sym (lemma-double-dual ⟦ mc ⟧ₘ₊) ⟩
  ⟦ mc ⟧ₘ₊ ∎
  where
  open ≡-Reasoning


aux-dual-SMC : ∀ smc -> dual ⟦ smc ⟧₁ ≡ ⟦ smc ⟧₁ ↑ 
aux-dual-SMC smc@(s , m , c) = begin
  dual ⟦ smc ⟧₁ ≡⟨ Eq.cong₂ _•_ (aux-dual-S^k (toℕ s)) (aux-dual-MC (m , c)) ⟩
  ⟦ smc ⟧₁ ↑ ∎
  where
  open ≡-Reasoning


aux-dual-SMC↑ : ∀ smc -> dual (⟦ smc ⟧₁ ↑) ≡ ⟦ smc ⟧₁
aux-dual-SMC↑ smc = begin
  dual (⟦ smc ⟧₁ ↑) ≡⟨ Eq.cong dual (Eq.sym (aux-dual-SMC smc)) ⟩
  dual (dual ⟦ smc ⟧₁) ≡⟨ Eq.sym (lemma-double-dual ⟦ smc ⟧₁) ⟩
  ⟦ smc ⟧₁ ∎
  where
  open ≡-Reasoning


open PB ((₂₊ n) QRel,_===_)
open PP ((₂₊ n) QRel,_===_)
open SR word-setoid
open Pattern-Assoc
open Lemmas0 (₁₊ n)
open Commuting-Symplectic n
open Sym0-Rewriting (₁₊ n)
open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
open import Examples.Groups.Symplectic.Lemmas.Ex-Rewriting p-2 p-prime
open Rewriting-Ex n

lemma-Ex-dual-gen : ∀ g -> [ dual-gen g ]ʷ ≈ Ex • [ g ]ʷ • Ex
lemma-Ex-dual-gen H-gen = rewrite-ex 100 auto
lemma-Ex-dual-gen S-gen = rewrite-ex 100 auto
lemma-Ex-dual-gen CZ-gen = rewrite-ex 100 auto
--lemma-Ex-dual-gen EX-gen = rewrite-ex 100 auto
lemma-Ex-dual-gen (H-gen ↥) = rewrite-ex 100 auto
lemma-Ex-dual-gen (S-gen ↥) = rewrite-ex 100 auto


lemma-Ex-dual : ∀ w -> dual w ≈ Ex • w • Ex
lemma-Ex-dual [ x ]ʷ = lemma-Ex-dual-gen x
lemma-Ex-dual ε = rewrite-ex 100 auto
lemma-Ex-dual (w • w₁) = begin
  dual (w • w₁) ≈⟨ cong (lemma-Ex-dual w) (lemma-Ex-dual w₁) ⟩
  (Ex • w • Ex) • Ex • w₁ • Ex ≈⟨ by-passoc (□ ^ 3 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
  (Ex • w) • (Ex • Ex) • w₁ • Ex ≈⟨ cright cleft rewrite-ex 100 auto ⟩
  (Ex • w) • ε • w₁ • Ex ≈⟨ cright left-unit ⟩
  (Ex • w) • w₁ • Ex ≈⟨ sym (trans (by-assoc auto) assoc) ⟩
  Ex • (w • w₁) • Ex ∎

lemma-Ex-dual' : ∀ w -> Ex • dual w • Ex ≈ w
lemma-Ex-dual' w = bbc Ex Ex aux
  where
  aux : Ex • (Ex • dual w • Ex) • Ex ≈ Ex • w • Ex
  aux = begin
    Ex • (Ex • dual w • Ex) • Ex ≈⟨ by-passoc (□ • □ ^ 3 • □) (□ ^ 2 • □ • □ ^ 2) auto ⟩
    (Ex • Ex) • dual w • (Ex • Ex) ≈⟨ cong lemma-order-Ex (cright lemma-order-Ex) ⟩
    ε • dual w • ε ≈⟨ trans left-unit right-unit ⟩
    dual w ≈⟨ lemma-Ex-dual w ⟩
    Ex • w • Ex ∎

aux-dual-Ex : dual Ex ≈ Ex
aux-dual-Ex = general-comm auto
