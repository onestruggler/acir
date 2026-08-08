{-# OPTIONS --cubical-compatible --safe #-}
--{-# OPTIONS --termination-depth=5 #-}

import Relation.Binary.Reasoning.Setoid as SR



open import Data.Product using (_,_ ; proj₁)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
import Data.Nat as Nat


open import Word.Base as WB hiding (wfoldl)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full



open import Data.Fin using (toℕ)
open import Data.Nat.Primality



module Examples.Groups.Symplectic.Lemmas.Embeding-2n (p-2 : ℕ) (p-prime : Prime (2+ p-2)) (n : ℕ)  where





open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime
open import Examples.Groups.Symplectic.NF2-Sym p-2 p-prime
open Lemmas-2Q 0
open Symplectic
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3 p-2 p-prime

open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
module L0 = Lemmas0 0

open LM2

open Symplectic
open Symplectic-GroupLike

open Duality





open PB ((₂₊ n) QRel,_===_)
open PP ((₂₊ n) QRel,_===_)
open Lemmas0 (₁₊ n)
open Lemmas-Sym
open SR word-setoid
open PB (₂ QRel,_===_)renaming (_===_ to _===₀_ ; _≈_ to _≈₀_) using ()


f : Gen 2 -> (Gen (₂₊ n))
f H-gen = H-gen
f S-gen = S-gen
f CZ-gen = CZ-gen
--f EX-gen = EX-gen
f (H-gen ↥) = H-gen ↥
f (S-gen ↥) = S-gen ↥

f* = wmap f

lemma-f* : ∀ w k -> f* (w ^ k) ≈ f* w ^ k
lemma-f* w k@0 = refl
lemma-f* w k@1 = refl
lemma-f* w k@(₂₊ k') = begin
  f* (w ^ k) ≈⟨ refl ⟩
  f* w • f* (w ^ (₁₊ k')) ≈⟨ cright lemma-f* w (₁₊ k') ⟩
  f* w • f* w ^ (₁₊ k') ≈⟨ sym (^-suc (f* w) (₁₊ k')) ⟩
  f* w ^ k ∎


lemma-f*-Sᵏ↑ : ∀ k -> f* ((S ^ k) ↑) ≈ (S ^ k) ↑
lemma-f*-Sᵏ↑ ₀ = refl
lemma-f*-Sᵏ↑ ₁ = refl
lemma-f*-Sᵏ↑ k@(₂₊ k') = begin
  f* ((S ^ k) ↑) ≈⟨ refl ⟩
  f* ((S • S ^ k'') ↑) ≈⟨ cong refl (lemma-f*-Sᵏ↑ (₁₊ k')) ⟩
  (S • S ^ k'') ↑ ≈⟨ refl ⟩
  (S ^ k) ↑ ∎
  where
  k'' = ₁₊ k'

lemma-f*-M : ∀ m -> f* (M m) ≈ M m
lemma-f*-M m = begin
  f* (M m) ≈⟨ cong (lemma-f* S (toℕ x)) (cright cong (lemma-f* S (toℕ x⁻¹)) (cright (cleft lemma-f* S (toℕ x)))) ⟩
  S^ x • H • S^ x⁻¹ • H • S^ x • H ≈⟨ refl ⟩
  M m ∎
  where
  x' = m
  x = x' .proj₁
  x⁻¹ = ((x' ⁻¹) .proj₁ )

lemma-f*-M↑ : ∀ m -> f* (M m ↑) ≈ M m ↑
lemma-f*-M↑ m = begin
  f* (M m ↑) ≈⟨ cong (lemma-f*-Sᵏ↑ (toℕ x)) (cright cong (lemma-f*-Sᵏ↑ (toℕ x⁻¹)) (cright (cleft lemma-f*-Sᵏ↑ (toℕ x)))) ⟩
  M m ↑ ∎
  where
  x' = m
  x = x' .proj₁
  x⁻¹ = ((x' ⁻¹) .proj₁ )


f-wd-ax : ∀ {w v} -> w ===₀ v -> (f*) w ≈ (f*) v
-- f-wd-ax def-EX = axiom def-EX
-- f-wd-ax order-EX = axiom order-EX
f-wd-ax (srel Base.order-S) = begin
  f* (S ^ p) ≈⟨ lemma-f* S p ⟩
  f* S ^ p ≈⟨ axiom order-S ⟩
  f* ε ∎
f-wd-ax (srel Base.order-H) = axiom order-H
f-wd-ax (srel Base.order-SH) = axiom order-SH
f-wd-ax (srel Base.comm-HHS) = axiom comm-HHS
f-wd-ax (srel (Base.M-mul x y)) = begin
  f* (M x • M y) ≈⟨ cong (lemma-f*-M x) (lemma-f*-M y) ⟩
  (M x • M y) ≈⟨ axiom (M-mul x y) ⟩
  (M (x *' y)) ≈⟨ sym (lemma-f*-M (x *' y)) ⟩
  f* (M (x *' y)) ∎
f-wd-ax (srel (Base.semi-MS x)) = begin
  f* (M x • S) ≈⟨ cleft lemma-f*-M x ⟩
  (M x • S) ≈⟨ axiom (semi-MS x) ⟩
  (S^ (x ^2) • M x) ≈⟨ sym (cong (lemma-f* S (toℕ (x ^2))) (lemma-f*-M x )) ⟩
  f* (S^ (x ^2) • M x) ∎
f-wd-ax (srel (Base.semi-M↑CZ x)) = begin
  f* ((M x ↑) • CZ) ≈⟨ cleft lemma-f*-M↑ x ⟩
  ((M x ↑) • CZ) ≈⟨ axiom (semi-M↑CZ x) ⟩
  (CZ^ (x ^1) • (M x ↑)) ≈⟨ sym (cong (lemma-f* CZ (toℕ (x ^1))) (lemma-f*-M↑ x)) ⟩
  f* (CZ^ (x ^1) • (M x ↑)) ∎
f-wd-ax (srel (Base.semi-M↓CZ x)) = begin
  f* ((M x ↓) • CZ) ≈⟨ cleft lemma-f*-M x ⟩
  ((M x ↓) • CZ) ≈⟨ axiom (semi-M↓CZ x) ⟩
  (CZ^ (x ^1) • (M x ↓)) ≈⟨ sym (cong (lemma-f* CZ (toℕ (x ^1))) (lemma-f*-M x)) ⟩
  f* (CZ^ (x ^1) • (M x ↓)) ∎
f-wd-ax (srel Base.order-CZ) = begin
  f* (CZ ^ p) ≈⟨ lemma-f* CZ p ⟩
  f* CZ ^ p ≈⟨ axiom order-CZ ⟩
  f* ε ∎
f-wd-ax (srel Base.comm-CZ-S↓) = axiom comm-CZ-S↓
f-wd-ax (srel Base.comm-CZ-S↑) = axiom comm-CZ-S↑
f-wd-ax (srel Base.selinger-c10) = begin
  f* (CZ • (H ↑) • CZ) ≈⟨ axiom selinger-c10 ⟩
  ((S⁻¹ ↑) • (H ↑) • (S⁻¹ ↑) • CZ • (H ↑) • (S⁻¹ ↑) • (S⁻¹ ↓)) ≈⟨ sym (cong (lemma-f*-Sᵏ↑ p-1) (cright cong (lemma-f*-Sᵏ↑ p-1) (cright (cright cong (lemma-f*-Sᵏ↑ p-1) (lemma-f* S p-1))))) ⟩
  f* ((S⁻¹ ↑) • (H ↑) • (S⁻¹ ↑) • CZ • (H ↑) • (S⁻¹ ↑) • (S⁻¹ ↓)) ∎
f-wd-ax (srel Base.selinger-c11) = begin
  f* (CZ • (H ↓) • CZ) ≈⟨ axiom selinger-c11 ⟩
  ((S⁻¹ ↓) • (H ↓) • (S⁻¹ ↓) • CZ • (H ↓) • (S⁻¹ ↓) • (S⁻¹ ↑)) ≈⟨ sym (cong (lemma-f* S p-1) (cright cong (lemma-f* S p-1) (cright (cright cong (lemma-f* S p-1) (lemma-f*-Sᵏ↑ p-1))))) ⟩
  f* ((S⁻¹ ↓) • (H ↓) • (S⁻¹ ↓) • CZ • (H ↓) • (S⁻¹ ↓) • (S⁻¹ ↑)) ∎
f-wd-ax (comm₁ H-gate H-gen) = axiom comm-H
f-wd-ax (comm₁ H-gate S-gen) = axiom comm-H
f-wd-ax (comm₁ S-gate H-gen) = axiom comm-S
f-wd-ax (comm₁ S-gate S-gen) = axiom comm-S
f-wd-ax (comm₂ _ ())
f-wd-ax (cong↑ (srel Base.order-S)) = begin
  f* ((S • S ^ ₁₊ p-2) ↑) ≈⟨  lemma-f*-Sᵏ↑ p ⟩
  ((S • S ^ ₁₊ p-2) ↑) ≈⟨ axiom (cong↑ order-S) ⟩
  f* (ε ↑) ∎
f-wd-ax (cong↑ (srel Base.order-H)) = axiom (cong↑ order-H)
f-wd-ax (cong↑ (srel Base.order-SH)) = axiom (cong↑ order-SH)
f-wd-ax (cong↑ (srel Base.comm-HHS)) = axiom (cong↑ comm-HHS)
f-wd-ax (cong↑ (srel (Base.M-mul x y))) = begin
  f* ((M x • M y) ↑) ≈⟨ cong (lemma-f*-M↑ x) (lemma-f*-M↑ y) ⟩
  (M x • M y) ↑ ≈⟨ axiom (cong↑ (M-mul x y)) ⟩
  (M (x *' y)) ↑ ≈⟨ sym (lemma-f*-M↑ (x *' y)) ⟩
  f* (M (x *' y) ↑) ∎
f-wd-ax (cong↑ (srel (Base.semi-MS x))) = begin
  f* ((M x • S) ↑) ≈⟨ cong (lemma-f*-M↑ x) (lemma-f*-Sᵏ↑ 1) ⟩
  (M x • S) ↑ ≈⟨ axiom (cong↑ (semi-MS x)) ⟩
  (S^ (x ^2) • M x) ↑ ≈⟨ sym (cong (lemma-f*-Sᵏ↑ (toℕ (x ^2))) (lemma-f*-M↑ x )) ⟩
  f* ((S^ (x ^2) • M x) ↑) ∎
f-wd-ax (cong↑ (comm₁ _ ()))
f-wd-ax (cong↑ (cong↑ (srel ())))


open import Presentation.Morphism _===₀_ ((₂₊ n) QRel,_===_)

by-emb : ∀ {w v} -> w ≈₀ v -> (f*) w ≈ (f*) v
by-emb {w} {v} eq = Congruence.fʷ-cong f f-wd-ax eq 

by-emb' : ∀ {w v w' v'} -> w ≈₀ v -> (f*) w ≈ w' -> (f*) v ≈ v' -> w' ≈ v'
by-emb' {w} {v} {w'} {v'} eq eqw eqv = begin
  w' ≈⟨ sym eqw ⟩
  (f*) w ≈⟨ by-emb eq ⟩
  (f*) v ≈⟨ eqv ⟩
  v' ∎

lemma-f*^^ : ∀ w k l -> f* ((w ^ k) ^ l) ≈ ((f* w) ^ k) ^ l
lemma-f*^^ w k l = begin
  f* ((w ^ k) ^ l) ≈⟨ (by-emb (P2.^^ w k l)) ⟩
  f* (w ^ (k Nat.* l)) ≈⟨ lemma-f* w (k Nat.* l) ⟩
  ((f* w) ^ (k Nat.* l)) ≈⟨ sym (^^ (f* w) k l) ⟩
  ((f* w) ^ k) ^ l ∎
  where
  module P2 = PP (2 QRel,_===_)

lemma-f*S^^↑  : ∀ k l -> f* (((S ^ k) ^ l) ↑) ≈ (((S) ^ k) ^ l) ↑
lemma-f*S^^↑ k l = begin
  f* (((S ^ k) ^ l) ↑) ≈⟨ (by-emb (lemma-cong↑ _ _ (P1.^^ S k l))) ⟩
  f* ((S ^ (k Nat.* l)) ↑) ≈⟨ lemma-f*-Sᵏ↑ (k Nat.* l) ⟩
  ((S) ^ (k Nat.* l)) ↑ ≈⟨ sym (lemma-cong↑ _ _ ( (Pn'.^^ (S) k l))) ⟩
  (((S) ^ k) ^ l) ↑ ∎
  where
  module P1 = PP (1 QRel,_===_)
  module P2 = PP (2 QRel,_===_)
  module Pn' = PP ((₁₊ n) QRel,_===_)
  

