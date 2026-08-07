{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS  --call-by-name #-}
{-# OPTIONS --termination-depth=4 #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq



open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Data.Bool hiding (_<_ ; _≤_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])

open import Data.Maybe
open import Data.Sum using ([_,_])

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations



open import Data.Fin using (toℕ)
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting using ()
open import Data.Nat.Primality



module Examples.Groups.Symplectic.BR.Two.Lemmas2 (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

n : ℕ
n = 0
    




open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime hiding (M)

open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Properties p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Soundness p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)
open import Examples.Groups.Symplectic.NF2-Sym p-2 p-prime
open LM2


open import Zp.ModularArithmetic
open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym3 p-2 p-prime
open import Examples.Groups.Symplectic.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2

open import Examples.Groups.Symplectic.ExtendedGate.NF1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3 p-2 p-prime
--open import Examples.Groups.Symplectic.Lemmas.Ex-Sym5 p-2 p-prime hiding (module L0)
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n p-2 p-prime

open import Examples.Groups.Symplectic.Lemmas.Lemma-Comm-n p-2 p-prime 0
open import Examples.Groups.Symplectic.Lemmas.Completeness1-Sym p-2 p-prime renaming (module Completeness to Cp1)
open Lemmas0a1
open Lemmas0c
open Lemmas-Sym

open import Examples.Groups.Symplectic.Lemmas.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()
--open import Examples.Groups.Symplectic.Lemmas.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to CP2) using ()
open import Examples.Groups.Symplectic.Lemmas.Lemmas-3Q p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.DH p-2 p-prime
open import Examples.Groups.Symplectic.BR.Calculations p-2 p-prime
open import Examples.Groups.Symplectic.BR.Two.Lemmas p-2 p-prime hiding (n ; sa ; module L01)


open PB ((₂₊ n) QRel,_===_)
open PP ((₂₊ n) QRel,_===_)
open SR word-setoid
open Pattern-Assoc
sa = by-passoc
open Lemmas0 n
module L01 = Lemmas0 (₁₊ n)
open Lemmas-2Q n
open Sym0-Rewriting (₁₊ n)
open Symplectic-GroupLike
open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike



lemma-CX^kCZ^l : ∀ (k*@(k , nz) : ℤ* ₚ) l ->
  let
  l/k = l * (k* ⁻¹) .proj₁
  lk = l * k
  in

  CX^ k • CZ^ l ≈ S^ l/k • CX^ k • S^ (- l/k) • S^ (- lk) ↑ 

lemma-CX^kCZ^l k*@(k , nz) l = bbc (M (k* ⁻¹) ↑) ε claim
  where
  k⁻¹ = (k* ⁻¹) .proj₁
  k⁻¹⁻¹ = (k* ⁻¹ ⁻¹) .proj₁
  a = l * k⁻¹
  claim : M (k* ⁻¹) ↑ • (CX^ k • CZ^ l) • ε ≈ M (k* ⁻¹) ↑ • (S^ a • CX^ k • S^ (- a) • S^ (- (l * k)) ↑) • ε
  claim = begin
    M (k* ⁻¹) ↑ • (CX^ k • CZ^ l) • ε ≈⟨ cright right-unit ⟩
    M (k* ⁻¹) ↑ • (CX^ k • CZ^ l) ≈⟨ sym assoc ⟩
    (M (k* ⁻¹) ↑ • CX^ k) • CZ^ l ≈⟨ cleft aux-M↑CX^k (k* ⁻¹) k ⟩
    (CX^ (k * k⁻¹) • M (k* ⁻¹) ↑) • CZ^ l ≈⟨ cleft cleft refl' (Eq.cong CX^ (lemma-⁻¹ʳ k {{nztoℕ {y = k} {neq0 = nz}}})) ⟩
    (CX • M (k* ⁻¹) ↑) • CZ^ l ≈⟨ assoc ⟩
    CX • M (k* ⁻¹) ↑ • CZ^ l ≈⟨ cright lemma-M↑CZ^k k⁻¹ l ((k* ⁻¹) .proj₂) ⟩
    CX • CZ^ (l * k⁻¹) • M (k* ⁻¹) ↑ ≈⟨ sym assoc ⟩
    (CX • CZ^ (l * k⁻¹)) • M (k* ⁻¹) ↑ ≈⟨ cleft lemma-semi-CXCZ^-alt a ⟩
    (S^ a • CX • S^ (- a) • S^ (- a) ↑ ) • M (k* ⁻¹) ↑ ≈⟨ sa (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    (S^ a • CX • S^ (- a)) • S^ (- a) ↑ • M (k* ⁻¹) ↑ ≈⟨ cright lemma-cong↑ _ _ (lemma-S^kM k⁻¹ (- a) ((k* ⁻¹) .proj₂)) ⟩
    (S^ a • CX • S^ (- a)) • M (k* ⁻¹) ↑ • S^ (- a * (k⁻¹⁻¹ * k⁻¹⁻¹)) ↑ ≈⟨ cright cright refl' (Eq.cong (\ xx -> S^ xx ↑) (Eq.cong (- a *_) (Eq.cong (\ xx -> xx * xx) (inv-involutive k*)))) ⟩
    (S^ a • CX • S^ (- a)) • M (k* ⁻¹) ↑ • S^ (- a * (k * k)) ↑ ≈⟨ cright cright refl' (Eq.cong (\ xx -> S^ xx ↑) (Eq.trans (Eq.sym (-‿distribˡ-* a (k * k))) (Eq.cong -_ (aux-lkkk'' k* l)))) ⟩
    (S^ a • CX • S^ (- a)) • M (k* ⁻¹) ↑ • S^ (- (l * k)) ↑ ≈⟨ sa (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (S^ a • CX) • (S^ (- a) • M (k* ⁻¹) ↑) • S^ (- (l * k)) ↑ ≈⟨ cright cleft lemma-comm-Sᵏ-w↑ (toℕ (- a)) (M (k* ⁻¹)) ⟩
    (S^ a • CX) • (M (k* ⁻¹) ↑ • S^ (- a)) • S^ (- (l * k)) ↑ ≈⟨ sym (sa (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto) ⟩
    (S^ a • CX • M (k* ⁻¹) ↑) • S^ (- a) • S^ (- (l * k)) ↑ ≈⟨ cleft cright (cleft refl' (Eq.cong CX^ (Eq.sym (lemma-⁻¹ʳ k {{nztoℕ {y = k} {neq0 = nz}}})))) ⟩
    (S^ a • CX^ (k * k⁻¹) • M (k* ⁻¹) ↑) • S^ (- a) • S^ (- (l * k)) ↑ ≈⟨ cleft cright sym (aux-M↑CX^k (k* ⁻¹) k) ⟩
    (S^ a • M (k* ⁻¹) ↑ • CX^ k) • S^ (- a) • S^ (- (l * k)) ↑ ≈⟨ sa (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 3) auto ⟩
    (S^ a • M (k* ⁻¹) ↑) • CX^ k • S^ (- a) • S^ (- (l * k)) ↑ ≈⟨ cleft lemma-comm-Sᵏ-w↑ (toℕ (a)) (M (k* ⁻¹)) ⟩
    (M (k* ⁻¹) ↑ • S^ a) • CX^ k • S^ (- a) • S^ (- (l * k)) ↑ ≈⟨ sa (□ ^ 2 • □ ^ 3) (□ ^ 5) auto ⟩
    M (k* ⁻¹) ↑ • S^ a • CX^ k • S^ (- a) • S^ (- (l * k)) ↑ ≈⟨ sym (cong refl right-unit) ⟩
    M (k* ⁻¹) ↑ • (S^ a • CX^ k • S^ (- a) • S^ (- (l * k)) ↑) • ε ∎


lemma-CX'^kCZ^l : ∀ (k*@(k , nz) : ℤ* ₚ) l ->
  let
  l/k = l * (k* ⁻¹) .proj₁
  lk = l * k
  in

  CX'^ k • CZ^ l ≈ S^ l/k • CX'^ k • S^ (- l/k) • S^ (- lk) ↑ 

lemma-CX'^kCZ^l k*@(k , nz) l = begin
  CX'^ k • CZ^ l ≈⟨ cleft sym (aux-CX^-CX'^ k) ⟩
  CX^ k • CZ^ l ≈⟨ lemma-CX^kCZ^l k* l ⟩
  S^ l/k • CX^ k • S^ (- l/k) • S^ (- lk) ↑ ≈⟨ cright cleft aux-CX^-CX'^ k ⟩
  S^ l/k • CX'^ k • S^ (- l/k) • S^ (- lk) ↑ ∎
  where
  l/k = l * (k* ⁻¹) .proj₁
  lk = l * k
  


lemma-semi-CX^kCZ^l : ∀ (k*@(k , nz) : ℤ* ₚ) l ->
  let
  l/k = l * (k* ⁻¹) .proj₁
  lk = l * k
  in

  CX^ k • CZ^ l ≈ S^ (- lk + - lk) ↑ • CZ^ l • CX^ k

lemma-semi-CX^kCZ^l k*@(k , nz) l = bbc (M (k* ⁻¹) ↑) ε claim
  where
  l/k = l * (k* ⁻¹) .proj₁
  lk = l * k
  k⁻¹ = (k* ⁻¹) .proj₁
  k⁻¹⁻¹ = (k* ⁻¹ ⁻¹) .proj₁
  a = l * k⁻¹
  aux : (- lk + - lk) * (k⁻¹ * k⁻¹) ≡ - a + - a
  aux = Eq.trans (*-distribʳ-+ (k⁻¹ * k⁻¹) (- lk) (- lk)) (Eq.cong (\ xx -> xx + xx) (Eq.trans (Eq.sym (-‿distribˡ-* lk ((k⁻¹ * k⁻¹)))) (Eq.cong -_ (aux-lkkk' k* l))))
  
  claim : M (k* ⁻¹) ↑ • (CX^ k • CZ^ l) • ε ≈ M (k* ⁻¹) ↑ • (S^ (- lk + - lk) ↑ • CZ^ l • CX^ k) • ε 
  claim = begin
    M (k* ⁻¹) ↑ • (CX^ k • CZ^ l) • ε ≈⟨ cright right-unit ⟩
    M (k* ⁻¹) ↑ • (CX^ k • CZ^ l) ≈⟨ sym assoc ⟩
    (M (k* ⁻¹) ↑ • CX^ k) • CZ^ l ≈⟨ cleft aux-M↑CX^k (k* ⁻¹) k ⟩
    (CX^ (k * k⁻¹) • M (k* ⁻¹) ↑) • CZ^ l ≈⟨ cleft cleft refl' (Eq.cong CX^ (lemma-⁻¹ʳ k {{nztoℕ {y = k} {neq0 = nz}}})) ⟩
    (CX • M (k* ⁻¹) ↑) • CZ^ l ≈⟨ assoc ⟩
    CX • M (k* ⁻¹) ↑ • CZ^ l ≈⟨ cright lemma-M↑CZ^k k⁻¹ l ((k* ⁻¹) .proj₂) ⟩
    CX • CZ^ (l * k⁻¹) • M (k* ⁻¹) ↑ ≈⟨ sym assoc ⟩
    (CX • CZ^ (l * k⁻¹)) • M (k* ⁻¹) ↑ ≈⟨ cleft lemma-semi-CXCZ^ a ⟩
    (S^ (- a + - a) ↑ • CZ^ a • CX) • M (k* ⁻¹) ↑  ≈⟨ sa (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (S^ (- a + - a) ↑ • CZ^ a) • CX • M (k* ⁻¹) ↑  ≈⟨ cright cleft sym (refl' (Eq.cong CX^ (lemma-⁻¹ʳ k {{nztoℕ {y = k} {neq0 = nz}}}))) ⟩
    (S^ (- a + - a) ↑ • CZ^ a) • CX^ (k * k⁻¹) • M (k* ⁻¹) ↑  ≈⟨ cright sym ( aux-M↑CX^k (k* ⁻¹) k) ⟩
    (S^ (- a + - a) ↑ • CZ^ a) • M (k* ⁻¹) ↑ • CX^ k  ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    S^ (- a + - a) ↑ • (CZ^ a • M (k* ⁻¹) ↑) • CX^ k  ≈⟨ cright cleft sym (lemma-M↑CZ^k k⁻¹ l ((k* ⁻¹) .proj₂)) ⟩
    S^ (- a + - a) ↑ • (M (k* ⁻¹) ↑ • CZ^ l) • CX^ k  ≈⟨ sym (sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
    (S^ (- a + - a) ↑ • M (k* ⁻¹) ↑) • CZ^ l • CX^ k  ≈⟨ cleft cleft refl' (Eq.cong (\ xx -> S^ xx ↑) (Eq.sym aux)) ⟩
    (S^ ((- lk + - lk) * (k⁻¹ * k⁻¹)) ↑ • M (k* ⁻¹) ↑) • CZ^ l • CX^ k  ≈⟨ sym (cleft lemma-cong↑ _ _ (lemma-MS^k k⁻¹ (- lk + - lk) ((k* ⁻¹) .proj₂))) ⟩
    (M (k* ⁻¹) ↑ • S^ ((- lk + - lk)) ↑) • CZ^ l • CX^ k  ≈⟨ assoc ⟩
    M (k* ⁻¹) ↑ • S^ (- lk + - lk) ↑ • CZ^ l • CX^ k  ≈⟨ sym (cong refl right-unit) ⟩
    M (k* ⁻¹) ↑ • (S^ (- lk + - lk) ↑ • CZ^ l • CX^ k) • ε ∎



lemma-semi-CX'^kCZ^l : ∀ (k*@(k , nz) : ℤ* ₚ) l ->
  let
  l/k = l * (k* ⁻¹) .proj₁
  lk = l * k
  in

  CX'^ k • CZ^ l ≈ S^ (- lk + - lk) ↑ • CZ^ l • CX'^ k

lemma-semi-CX'^kCZ^l k*@(k , nz) l = begin
  CX'^ k • CZ^ l ≈⟨ cleft sym (aux-CX^-CX'^ k) ⟩
  CX^ k • CZ^ l ≈⟨ lemma-semi-CX^kCZ^l k* l ⟩
  S^ (- lk + - lk) ↑ • CZ^ l • CX^ k ≈⟨ cright cright aux-CX^-CX'^ k ⟩
  S^ (- lk + - lk) ↑ • CZ^ l • CX'^ k ∎
  where
  l/k = l * (k* ⁻¹) .proj₁
  lk = l * k


aux-Ex-alt : ∀ (b*@(b , nzb) : ℤ* ₚ) ->
  let b⁻¹ = (b* ⁻¹) .proj₁ in
  
  M b* • Ex • M (b*) ≈ CZ^ b • H • H ↑ • CZ^ b⁻¹ • H • H ↑ • CZ^ b • H • H ↑
  
aux-Ex-alt b*@(b , nzb) = bbc ε (M b*⁻¹) claim
  where
  b⁻¹ = (b* ⁻¹) .proj₁
  b*⁻¹ = b* ⁻¹
  claim : ε • (M b* • Ex • M (b*)) • M (b* ⁻¹) ≈ ε • (CZ^ b • H • H ↑ • CZ^ b⁻¹ • H • H ↑ • CZ^ b • H • H ↑) • M (b* ⁻¹)
  claim = begin
    ε • (M b* • Ex • M (b* )) • M b*⁻¹ ≈⟨ left-unit ⟩
    (M b* • Ex • M (b* )) • M b*⁻¹ ≈⟨ sa (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (M b* • Ex) • M (b* ) • M b*⁻¹ ≈⟨ cright L01.aux-M-mul b* ⟩
    (M b* • Ex) • ε ≈⟨ right-unit ⟩
    M b* • Ex ≈⟨ cright refl ⟩
    M b* • CZ • H • H ↑ • CZ • H • H ↑ • CZ • H • H ↑ ≈⟨ sym assoc ⟩
    (M b* • CZ) • H • H ↑ • CZ • H • H ↑ • CZ • H • H ↑ ≈⟨ cleft axiom (semi-M↓CZ b*) ⟩
    (CZ^ b • M b*) • H • H ↑ • CZ • H • H ↑ • CZ • H • H ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    CZ^ b • (M b* • H) • H ↑ • CZ • H • H ↑ • CZ • H • H ↑ ≈⟨ cright cleft sym (semi-HM' b*) ⟩
    CZ^ b • (H • M (b* ⁻¹)) • H ↑ • CZ • H • H ↑ • CZ • H • H ↑ ≈⟨ sa (□ • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (CZ^ b • H) • (M (b* ⁻¹) • H ↑) • CZ • H • H ↑ • CZ • H • H ↑ ≈⟨ cright cleft aux-comm-m-H↑ (b* ⁻¹) ⟩
    (CZ^ b • H) • (H ↑ • M (b* ⁻¹)) • CZ • H • H ↑ • CZ • H • H ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □) auto ⟩
    (CZ^ b • H • H ↑) • (M (b* ⁻¹) • CZ) • H • H ↑ • CZ • H • H ↑ ≈⟨ cright cleft axiom (semi-M↓CZ (b* ⁻¹)) ⟩
    (CZ^ b • H • H ↑) • (CZ^ b⁻¹ • M (b* ⁻¹)) • H • H ↑ • CZ • H • H ↑ ≈⟨ sa (□ ^ 3 • □ ^ 2 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □) auto ⟩
    (CZ^ b • H • H ↑ • CZ^ b⁻¹) • (M (b* ⁻¹) • H) • H ↑ • CZ • H • H ↑ ≈⟨ cright cleft sym (L01.semi-HM b*) ⟩
    (CZ^ b • H • H ↑ • CZ^ b⁻¹) • (H • M b*) • H ↑ • CZ • H • H ↑ ≈⟨ sa (□ ^ 4 • □ ^ 2 • □ ^ 2) (□ ^ 5 • □ ^ 2 • □) auto ⟩
    (CZ^ b • H • H ↑ • CZ^ b⁻¹ • H) • (M b* • H ↑) • CZ • H • H ↑ ≈⟨ cright cleft aux-comm-m-H↑ (b*) ⟩
    (CZ^ b • H • H ↑ • CZ^ b⁻¹ • H) • (H ↑ • M b*) • CZ • H • H ↑ ≈⟨ sa (□ ^ 5 • □ ^ 2 • □ ^ 2) (□ ^ 6 • □ ^ 2 • □) auto ⟩
    (CZ^ b • H • H ↑ • CZ^ b⁻¹ • H • H ↑) • (M b* • CZ) • H • H ↑ ≈⟨ cright cleft axiom (semi-M↓CZ b*) ⟩
    (CZ^ b • H • H ↑ • CZ^ b⁻¹ • H • H ↑) • (CZ^ b • M b*) • H • H ↑ ≈⟨ sa (□ ^ 6 • □ ^ 2 • □ ^ 2) (□ ^ 7 • □ ^ 2 • □) auto ⟩
    (CZ^ b • H • H ↑ • CZ^ b⁻¹ • H • H ↑ • CZ^ b) • (M b* • H) • H ↑ ≈⟨ cright cleft sym (semi-HM' b*) ⟩
    (CZ^ b • H • H ↑ • CZ^ b⁻¹ • H • H ↑ • CZ^ b) • (H • M b*⁻¹) • H ↑ ≈⟨ sa (□ ^ 7 • □ ^ 2 • □ ^ 2) (□ ^ 8 • □ ^ 2) auto ⟩
    (CZ^ b • H • H ↑ • CZ^ b⁻¹ • H • H ↑ • CZ^ b • H) • M b*⁻¹ • H ↑ ≈⟨ cright aux-comm-m-H↑ (b* ⁻¹) ⟩
    (CZ^ b • H • H ↑ • CZ^ b⁻¹ • H • H ↑ • CZ^ b • H) • H ↑ • M b*⁻¹ ≈⟨ sa (□ ^ 8 • □ ^ 2) (□ ^ 9 • □ ^ 1) auto ⟩
    (CZ^ b • H • H ↑ • CZ^ b⁻¹ • H • H ↑ • CZ^ b • H • H ↑) • M b*⁻¹ ≈⟨ sym left-unit ⟩
    ε • (CZ^ b • H • H ↑ • CZ^ b⁻¹ • H • H ↑ • CZ^ b • H • H ↑) • M b*⁻¹ ∎



aux-hEx-alt : ∀ (b*@(b , nzb) : ℤ* ₚ) ->
  let b⁻¹ = (b* ⁻¹) .proj₁ in
   
  (M b* • Ex • M b*) • H ↑ ^ 3 • H ^ 3 • CZ^ (- b) • H ↑ ^ 3 • H ^ 3 ≈ CZ^ b • H • H ↑ • CZ^ b⁻¹

aux-hEx-alt b*@(b , nzb) = bbc ε (H • H ↑ • CZ^ b • H • H ↑) claim
  where
  b⁻¹ = (b* ⁻¹) .proj₁
  b*⁻¹ = b* ⁻¹
  claim : ε • ( (M b* • Ex • M b*) • H ↑ ^ 3 • H ^ 3 • CZ^ (- b) • H ↑ ^ 3 • H ^ 3 ) • (H • H ↑ • CZ^ b • H • H ↑) ≈ ε • ( CZ^ b • H • H ↑ • CZ^ b⁻¹ ) • (H • H ↑ • CZ^ b • H • H ↑)
  claim = begin
    ε • ( (M b* • Ex • M b*) • H ↑ ^ 3 • H ^ 3 • CZ^ (- b) • H ↑ ^ 3 • H ^ 3 ) • (H • H ↑ • CZ^ b • H • H ↑) ≈⟨ left-unit ⟩
    ( (M b* • Ex • M b*) • H ↑ ^ 3 • H ^ 3 • CZ^ (- b) • H ↑ ^ 3 • H ^ 3 ) • (H • H ↑ • CZ^ b • H • H ↑) ≈⟨ sa (□ ^ 6 • □ ^ 5) (□ ^ 4 • □ ^ 4 • □ ^ 3) auto ⟩
    ( (M b* • Ex • M b*) • H ↑ ^ 3 • H ^ 3 • CZ^ (- b)) • (H ↑ ^ 3 • H ^ 3  • H • H ↑) • CZ^ b • H • H ↑ ≈⟨ cright cleft rewrite-sym0 100 auto ⟩
    ( (M b* • Ex • M b*) • H ↑ ^ 3 • H ^ 3 • CZ^ (- b)) • ε • CZ^ b • H • H ↑ ≈⟨ cright left-unit ⟩
    ( (M b* • Ex • M b*) • H ↑ ^ 3 • H ^ 3 • CZ^ (- b)) • CZ^ b • H • H ↑ ≈⟨ sa (□ ^ 4 • □ ^ 3) (□ ^ 3 • □ ^ 2 • □ ^ 2) auto ⟩
    ( (M b* • Ex • M b*) • H ↑ ^ 3 • H ^ 3) • (CZ^ (- b) • CZ^ b) • H • H ↑ ≈⟨ cright cleft lemma-CZ^k+l (- b) b ⟩
    ( (M b* • Ex • M b*) • H ↑ ^ 3 • H ^ 3) • CZ^ (- b + b) • H • H ↑ ≈⟨ cright cleft refl' (Eq.cong CZ^ (+-inverseˡ b)) ⟩
    ( (M b* • Ex • M b*) • H ↑ ^ 3 • H ^ 3) • ε • H • H ↑ ≈⟨ trans assoc (cong refl assoc) ⟩
    (M b* • Ex • M b*) • H ↑ ^ 3 • H ^ 3 • ε • H • H ↑ ≈⟨ cright rewrite-sym0 100 auto ⟩
    (M b* • Ex • M b*) • ε ≈⟨ right-unit ⟩
    (M b* • Ex • M b*) ≈⟨ aux-Ex-alt (b , nzb) ⟩
    CZ^ b • H • H ↑ • CZ^ b⁻¹ • H • H ↑ • CZ^ b • H • H ↑ ≈⟨ sa (□ ^ 9) (□ ^ 4 • □ ^ 5) auto ⟩
    ( CZ^ b • H • H ↑ • CZ^ b⁻¹ ) • (H • H ↑ • CZ^ b • H • H ↑) ≈⟨ sym left-unit ⟩
    ε • ( CZ^ b • H • H ↑ • CZ^ b⁻¹ ) • (H • H ↑ • CZ^ b • H • H ↑) ∎

