{-# OPTIONS  --safe #-}
--{-# OPTIONS --termination-depth=5 #-}
open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_ ; id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; ∃ ; Σ ; Σ-syntax)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
import Data.Nat as Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
import Data.Vec as Vec
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_] ; [_,_]′)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Word.Base as WB hiding (wfoldl)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.CosetNF as CA
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)
import Presentation.Construct.Properties.SemiDirectProduct2 as SDP2
import Presentation.Construct.Properties.DirectProduct as DP
import Examples.Groups.Cyclic.Cyclic as Cyclic


open import Data.Fin using (Fin ; toℕ ; suc ; zero ; fromℕ)
open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_])
open import Data.Nat.Primality



module Examples.Groups.Symplectic.Embeding-1n (p-2 : ℕ) (p-prime : Prime (2+ p-2)) (n : ℕ)  where





open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Symplectic p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas-2Qupit-Sym p-2 p-prime
open import Examples.Groups.Symplectic.NF2-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Cosets p-2 p-prime
open Lemmas-2Q 0
open Symplectic
open import Examples.Groups.Symplectic.NF1-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Ex-Sym3 p-2 p-prime

open import Examples.Groups.Symplectic.Lemma-Comm p-2 p-prime
open import Examples.Groups.Symplectic.Lemma-Postfix p-2 p-prime
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
module L0 = Lemmas0 0

open LM2
open import Examples.Groups.Symplectic.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()

open Symplectic
open Symplectic-GroupLike

open import Data.Nat.DivMod
open import Data.Fin.Properties
open Duality
open import Algebra.Properties.Ring (+-*-ring p-2)




open import Relation.Unary

open PB ((₁₊ n) QRel,_===_)
open PP ((₁₊ n) QRel,_===_)
open Lemmas0 n
open Lemmas-Sym
open SR word-setoid
open PB (₁ QRel,_===_)renaming (_===_ to _===₀_ ; _≈_ to _≈₀_) using ()


f : Gen 1 -> (Gen (₁₊ n))
f H-gen = H-gen
f S-gen = S-gen

f* = wmap f

lemma-f* : ∀ w k -> f* (w ^ k) ≈ f* w ^ k
lemma-f* w k@0 = refl
lemma-f* w k@1 = refl
lemma-f* w k@(₂₊ k') = begin
  f* (w ^ k) ≈⟨ refl ⟩
  f* w • f* (w ^ (₁₊ k')) ≈⟨ cright lemma-f* w (₁₊ k') ⟩
  f* w • f* w ^ (₁₊ k') ≈⟨ sym (^-suc (f* w) (₁₊ k')) ⟩
  f* w ^ k ∎

lemma-f*-M : ∀ m -> f* (M m) ≈ M m
lemma-f*-M m = begin
  f* (M m) ≈⟨ cong (lemma-f* S (toℕ x)) (cright cong (lemma-f* S (toℕ x⁻¹)) (cright (cleft lemma-f* S (toℕ x)))) ⟩
  S^ x • H • S^ x⁻¹ • H • S^ x • H ≈⟨ refl ⟩
  M m ∎
  where
  x' = m
  x = x' .proj₁
  x⁻¹ = ((x' ⁻¹) .proj₁ )


f-wd-ax : ∀ {w v} -> w ===₀ v -> (f*) w ≈ (f*) v
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
f-wd-ax (cong↑ (srel ()))


open import Presentation.Morphism _===₀_ ((₁₊ n) QRel,_===_)

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
  f* ((w ^ k) ^ l) ≈⟨ (by-emb (P1.^^ w k l)) ⟩
  f* (w ^ (k Nat.* l)) ≈⟨ lemma-f* w (k Nat.* l) ⟩
  ((f* w) ^ (k Nat.* l)) ≈⟨ sym (^^ (f* w) k l) ⟩
  ((f* w) ^ k) ^ l ∎
  where
  module P1 = PP (₁ QRel,_===_)

