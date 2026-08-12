------------------------------------------------------------------------
-- Presentations of groups
--
-- The duality involution on symplectic circuits.
--
-- Exchanging the two coordinates of each wire, and the lemmas
-- identifying a circuit's dual with its image under that exchange.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_)

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃ ; Σ-syntax)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
import Data.Nat as Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full


import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_])
open import Data.Nat.Primality

open import Notations
import Circuit.Base

module Examples.Groups.Symplectic.Syntactics.Duality (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Syntactics.Gates p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics.Derived p-2 p-prime

module Lemmas3 where
  variable
    n : ℕ

  open Symplectic
  open import ForStdlib.Data.Fin.Mod
--  open Rewriting-Symplectic
  open Rewriting


  lemma-comm-Ex-w↑↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    Ex • w ↑ ↑ ≈ w ↑ ↑ • Ex
    
  lemma-comm-Ex-w↑↑ {n} [ H-gen ]ʷ = general-comm auto
    where
    open Commuting-Symplectic n
    
  -- lemma-comm-Ex-w↑↑ {n} [ EX-gen ]ʷ = general-comm auto
  --   where
  --   open Commuting-Symplectic n
    
  lemma-comm-Ex-w↑↑ {n} [ S-gen ]ʷ = general-comm auto
    where
    open Commuting-Symplectic n
  lemma-comm-Ex-w↑↑ {n} [ CZ-gen ]ʷ = general-comm auto
    where
    open Commuting-Symplectic n
  lemma-comm-Ex-w↑↑ {n} [ x ↥ ]ʷ = begin
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (([ x ↥ ]ʷ ↑) ↑) ≈⟨ by-assoc auto ⟩
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓) • H ↑ • [ x ↥ ]ʷ ↑ ↑ ≈⟨ cong refl (sym (axiom (cong↑ comm-H))) ⟩
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓) • [ x ↥ ]ʷ ↑ ↑ • H ↑ ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) • H ↓ • [ x ↥ ]ʷ ↑ ↑) • H ↑ ≈⟨ cong (cong refl (sym (axiom comm-H))) refl ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) • [ x ↥ ]ʷ ↑ ↑ • H ↓) • H ↑ ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ • [ x ↥ ]ʷ ↑ ↑) • (H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-CZ))) refl ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • [ x ↥ ]ʷ ↑ ↑ • CZ) • (H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓) • H ↑ • [ x ↥ ]ʷ ↑ ↑) • (CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom (cong↑ comm-H)))) refl ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓) • [ x ↥ ]ʷ ↑ ↑ • H ↑) • (CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓ • H ↑ • CZ) • H ↓ • [ x ↥ ]ʷ ↑ ↑) • (H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-H))) refl ⟩
    ((CZ • H ↓ • H ↑ • CZ) • [ x ↥ ]ʷ ↑ ↑ • H ↓) • (H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓ • H ↑) • CZ • [ x ↥ ]ʷ ↑ ↑) • (H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-CZ))) refl ⟩
    ((CZ • H ↓ • H ↑) • [ x ↥ ]ʷ ↑ ↑ • CZ) • (H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓) • H ↑ • [ x ↥ ]ʷ ↑ ↑) • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom (cong↑ comm-H)))) refl ⟩
    ((CZ • H ↓) • [ x ↥ ]ʷ ↑ ↑ • H ↑) • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    (CZ • H ↓ • [ x ↥ ]ʷ ↑ ↑) • (H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-H))) refl ⟩
    (CZ • [ x ↥ ]ʷ ↑ ↑ • H ↓) • (H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    (CZ • [ x ↥ ]ʷ ↑ ↑) • (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong ( (sym (axiom comm-CZ))) refl ⟩
    ([ x ↥ ]ʷ ↑ ↑ • CZ) • (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    [ x ↥ ]ʷ ↑ ↑ • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ refl ⟩
    (([ x ↥ ]ʷ ↑) ↑) • Ex ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
  lemma-comm-Ex-w↑↑ {n} ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
  lemma-comm-Ex-w↑↑ {n} (w • v) = begin
    Ex • (((w • v) ↑) ↑) ≈⟨ refl ⟩
    Ex • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
    (Ex • w ↑ ↑) • v ↑ ↑ ≈⟨ cong (lemma-comm-Ex-w↑↑ w) refl ⟩
    (w ↑ ↑ • Ex) • v ↑ ↑ ≈⟨ assoc ⟩
    w ↑ ↑ • Ex • v ↑ ↑ ≈⟨ cong refl (lemma-comm-Ex-w↑↑ v) ⟩
    w ↑ ↑ • v ↑ ↑ • Ex ≈⟨ sym assoc ⟩
    (((w • v) ↑) ↑) • Ex ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid


-- ----------------------------------------------------------------------
-- * Duality

module Duality where

  open Symplectic
  open Commuting-Symplectic
  open Rewriting
  open Symplectic

  private
    variable
      n : ℕ

  -- Here, we provide a proof principle for duality (an equation is
  -- provable iff its dual is provable).


  -- Each generator has a dual, obtained by swapping the two qubits.
  dual-gen : Gen 2 → Gen 2
  dual-gen (gate₁ H-gate)        = gate₁ H-gate ↥
  dual-gen (gate₁ S-gate)        = gate₁ S-gate ↥
  dual-gen (gate₂ CZ-gate)       = gate₂ CZ-gate
--  dual-gen EX-gen = EX-gen
  dual-gen (gate₁ H-gate ↥)      = gate₁ H-gate
  dual-gen (gate₁ S-gate ↥)      = gate₁ S-gate
  dual-gen (((gate₀ ()) ↥) ↥)
  

  -- Compute the dual of a word.
  dual : Word (Gen 2) → Word (Gen 2)
  dual [ x ]ʷ = [ (dual-gen x) ]ʷ
  dual ε = ε
  dual (w • u) = dual w • dual u

  -- Lemma: duality is an involution.
  lemma-double-dual : ∀ w → w ≡ dual (dual w)
  lemma-double-dual ([ gate₁ H-gate ]ʷ)       = Eq.refl
  lemma-double-dual ([ gate₁ H-gate ↥ ]ʷ)     = Eq.refl
  lemma-double-dual ([ gate₁ S-gate ]ʷ)       = Eq.refl
  lemma-double-dual ([ gate₁ S-gate ↥ ]ʷ)     = Eq.refl
  lemma-double-dual ([ gate₂ CZ-gate ]ʷ)      = Eq.refl
  lemma-double-dual ([ ((gate₀ ()) ↥) ↥ ]ʷ)
--  lemma-double-dual ([ EX-gen ]ʷ) = Eq.refl
  lemma-double-dual ε = Eq.refl
  lemma-double-dual (w • v) = Eq.cong₂ _•_ (lemma-double-dual w) (lemma-double-dual v)


  aux-dual : ∀ w k → dual (w ^ k) ≡ dual w ^ k
  aux-dual w k@0 = auto
  aux-dual w k@1 = auto
  aux-dual w k@(₂₊ k') = begin
    dual (w ^ k) ≡⟨ auto ⟩
    dual w • dual (w ^ ₁₊ k') ≡⟨ (Eq.cong (dual w •_) (aux-dual w (₁₊ k'))) ⟩
    dual w • dual w ^ ₁₊ k' ≡⟨ auto ⟩
    dual w ^ k ∎
    where
    open ≡-Reasoning

  aux-↑ : ∀ (w : Word (Gen n)) k → w ↑ ^ k ≡ (w ^ k) ↑
  aux-↑ w k@0 = auto
  aux-↑ w k@1 = auto
  aux-↑ w k@(₂₊ k') = begin
    w ↑ ^ k ≡⟨ auto ⟩
    w ↑ • w ↑ ^ (₁₊ k') ≡⟨ (Eq.cong (w ↑ •_)  (aux-↑ w (₁₊ k'))) ⟩
    w ↑ • (w ^ (₁₊ k')) ↑ ≡⟨ auto ⟩
    (w ^ k) ↑ ∎
    where
    open ≡-Reasoning

  aux-dual-S⁻¹↑ : dual (S⁻¹ ↑) ≡ S⁻¹
  aux-dual-S⁻¹↑ = begin
    dual (S⁻¹ ↑) ≡⟨ Eq.cong dual (Eq.sym (aux-↑ S p-1)) ⟩
    dual (S ↑ ^ p-1) ≡⟨ aux-dual (S ↑) p-1 ⟩
    S⁻¹ ∎
    where
    open ≡-Reasoning

  aux-dual-S^k↑ : ∀ k → dual ((S ^ k) ↑) ≡ S ^ k
  aux-dual-S^k↑ k = begin
    dual ((S ^ k) ↑) ≡⟨ Eq.cong dual (Eq.sym (aux-↑ S k)) ⟩
    dual (S ↑ ^ k) ≡⟨ aux-dual (S ↑) k ⟩
    S ^ k ∎
    where
    open ≡-Reasoning

  aux-dual-S⁻¹ : dual (S⁻¹ ↓) ≡ (S⁻¹ ↑)
  aux-dual-S⁻¹ = begin
    dual (S⁻¹ ↓) ≡⟨ aux-dual S p-1 ⟩
    S ↑ ^ p-1 ≡⟨ aux-↑ S p-1 ⟩
    (S⁻¹ ↑) ∎
    where
    open ≡-Reasoning

  aux-dual-S^k : ∀ k → dual ((S ^ k) ↓) ≡ (S ^ k) ↑
  aux-dual-S^k k = begin
    dual ((S ^ k) ↓) ≡⟨ aux-dual S k ⟩
    S ↑ ^ k ≡⟨ aux-↑ S k ⟩
    (S ^ k) ↑ ∎
    where
    open ≡-Reasoning


  aux-dual-CZ^k : ∀ k → dual ((CZ ^ k)) ≡ (CZ ^ k)
  aux-dual-CZ^k k = begin
    dual ((CZ ^ k)) ≡⟨ aux-dual CZ k ⟩
    CZ ^ k ≡⟨ auto ⟩
    (CZ ^ k) ∎
    where
    open ≡-Reasoning


  aux-dual-Mx : ∀ x → dual (M x) ≡ M x ↑
  aux-dual-Mx x' = begin
    dual (S^ x • H • S^ x⁻¹ • H • S^ x • H) ≡⟨ Eq.cong₂ (\ xx yy → xx • H ↑ • yy • dual(H • S^ x • H)) (aux-dual-S^k (toℕ x)) (aux-dual-S^k (toℕ x⁻¹)) ⟩
    S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • dual (H • S^ x • H) ≡⟨ Eq.cong (\ xx → S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • (H ↑ • xx • H ↑)) (aux-dual-S^k (toℕ x)) ⟩
    M x' ↑ ∎
    where
    open ≡-Reasoning
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )


  aux-dual-Mx↑ : ∀ x → dual (M x ↑) ≡ M x
  aux-dual-Mx↑ x' = begin
    dual (S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • S^ x ↑ • H ↑) ≡⟨ Eq.cong₂ (\ xx yy → xx • H • yy • dual(H ↑ • S^ x ↑ • H ↑)) (aux-dual-S^k↑ (toℕ x)) (aux-dual-S^k↑ (toℕ x⁻¹)) ⟩
    S^ x • H • S^ x⁻¹ • dual (H ↑ • S^ x ↑ • H ↑) ≡⟨ Eq.cong (\ xx → S^ x • H • S^ x⁻¹ • (H • xx • H)) (aux-dual-S^k↑ (toℕ x)) ⟩
    M x' ∎
    where
    open ≡-Reasoning
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

  -- Dualize a proof. Duality is useful early on. However, we will not
  -- prove the duals of axioms rel-A, rel-B, and rel-C until much
  -- later. Therefore, we work only with Clifford relations for the
  -- time being.
  open PB (2 QRel,_===_)
  open PP (2 QRel,_===_)
  open SR word-setoid


  lemma-dual : ∀ {w u} → w === u → dual w ≈ dual u
  -- lemma-dual def-EX = begin
  --   EX ≈⟨ axiom def-EX ⟩
  --   Ex ≈⟨ general-comm 0 auto ⟩
  --   dual Ex ∎
  -- lemma-dual order-EX = axiom order-EX
  lemma-dual (srel Base.order-S) = begin
    S ↑ • dual (S ^ ₁₊ p-2) ≈⟨ (cright (refl' (aux-dual S p-1))) ⟩
    S ↑ • dual S ^ ₁₊ p-2 ≈⟨ refl ⟩
    S ↑ • (S ↑) ^ ₁₊ p-2 ≈⟨ (cright (refl' (aux-↑ S p-1))) ⟩
    (S ^ p) ↑ ≈⟨ axiom (cong↑ order-S) ⟩
    ε ∎
  lemma-dual (srel Base.order-H) = axiom (cong↑ order-H)
  lemma-dual (srel Base.order-SH) = axiom (cong↑ order-SH)
  lemma-dual (srel Base.comm-HHS) = axiom (cong↑ comm-HHS)
  lemma-dual (srel (Base.M-mul x y)) = begin
    dual (M x • M y) ≈⟨ cong (refl' (aux-dual-Mx x)) (refl' (aux-dual-Mx y)) ⟩
    (M x • M y) ↑ ≈⟨ axiom (cong↑ (M-mul x y)) ⟩
    M (x *' y) ↑ ≈⟨ refl' ((Eq.sym  (aux-dual-Mx (x *' y)))) ⟩
    dual (M (x *' y)) ∎
  lemma-dual (srel (Base.semi-MS x)) = begin
    dual (M x • S) ≈⟨ (cleft refl' (aux-dual-Mx x)) ⟩
    (M x • S) ↑ ≈⟨ axiom (cong↑ (semi-MS x)) ⟩
    (S^ (x ^2) • M x) ↑ ≈⟨ cong (refl' (Eq.sym (aux-dual-S^k (toℕ (fromℕ< _))))) (refl' (Eq.sym (aux-dual-Mx x))) ⟩
    dual (S^ (x ^2) • M x) ∎
  lemma-dual (srel (Base.semi-M↑CZ x)) = begin
    dual (M x ↑ • CZ) ≈⟨ (cleft refl' (aux-dual-Mx↑ x)) ⟩
    (M x • CZ) ≈⟨ axiom (semi-M↓CZ x) ⟩
    (CZ^ (x ^1) • M x) ≈⟨ cong (refl' (Eq.sym (aux-dual-CZ^k (toℕ (x .proj₁))))) (sym (refl' (aux-dual-Mx↑ x))) ⟩
    dual (CZ^ (x ^1) • M x ↑) ∎
  lemma-dual (srel (Base.semi-M↓CZ x)) = begin
    dual (M x • CZ) ≈⟨ (cleft refl' (aux-dual-Mx x)) ⟩
    (M x ↑ • CZ) ≈⟨ axiom (semi-M↑CZ x) ⟩
    (CZ^ (x ^1) • M x ↑) ≈⟨ cong (refl' (Eq.sym (aux-dual-CZ^k (toℕ (x .proj₁))))) (sym (refl' (aux-dual-Mx x))) ⟩
    dual (CZ^ (x ^1) • M x) ∎
  lemma-dual (srel Base.order-CZ) = begin
    CZ • dual (CZ ^ ₁₊ p-2) ≈⟨ (cright (refl' (aux-dual CZ p-1))) ⟩
    CZ • dual CZ ^ ₁₊ p-2 ≈⟨ refl ⟩
    (CZ ^ p) ≈⟨ axiom (order-CZ) ⟩
    ε ∎
  lemma-dual (srel Base.comm-CZ-S↓) = axiom comm-CZ-S↑
  lemma-dual (srel Base.comm-CZ-S↑) = axiom comm-CZ-S↓
  lemma-dual (srel Base.selinger-c10) = begin
    dual (CZ • H ↑ • CZ) ≈⟨ refl ⟩
    (CZ • H • CZ) ≈⟨ axiom selinger-c11 ⟩
    S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑ ≈⟨ sym (cong (refl' aux-dual-S⁻¹↑) (cright cong (refl' aux-dual-S⁻¹↑) (cright (cright cong (refl' aux-dual-S⁻¹↑) (refl' aux-dual-S⁻¹))))) ⟩
    dual (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) ∎
  lemma-dual (srel Base.selinger-c11) = begin
    dual (CZ • H ↓ • CZ) ≈⟨ refl ⟩
    (CZ • H ↑ • CZ) ≈⟨ axiom selinger-c10 ⟩
    S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ≈⟨ sym (cong (refl' aux-dual-S⁻¹) (cright cong (refl' aux-dual-S⁻¹) (cright (cright cong (refl' aux-dual-S⁻¹) (refl' aux-dual-S⁻¹↑))))) ⟩
    dual (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑) ∎
  lemma-dual (comm₁ H-gate (gate₁ S-gate)) = sym (axiom comm-S)
  lemma-dual (comm₁ H-gate (gate₁ H-gate)) = sym (axiom comm-H)
  lemma-dual (comm₁ S-gate (gate₁ S-gate)) = sym (axiom comm-S)
  lemma-dual (comm₁ S-gate (gate₁ H-gate)) = sym (axiom comm-H)
  -- The shifted generator can now sit at width 0, where only gate₀ lives.
  lemma-dual (comm₁ h (gate₀ ()))
  lemma-dual (comm₁ h ((gate₀ ()) ↥))
  lemma-dual (comm₂ h (gate₀ ()))
  lemma-dual (cong↑ (comm₁ h (gate₀ ())))
  lemma-dual (cong↑ (srel Base.order-S)) = begin
     S • dual ((S ^ p-1) ↑) ≈⟨ (cright refl' (Eq.cong dual (Eq.sym (aux-↑ S p-1)))) ⟩
     S • dual ((S ↑ ^ p-1)) ≈⟨ (cright refl' ( aux-dual (S ↑) p-1)) ⟩
     S • dual (S ↑) ^ p-1 ≈⟨ axiom order-S ⟩
     ε ∎
  lemma-dual (cong↑ (srel Base.order-H)) = axiom order-H
  lemma-dual (cong↑ (srel Base.order-SH)) = axiom order-SH
  lemma-dual (cong↑ (srel Base.comm-HHS)) = axiom comm-HHS
  lemma-dual (cong↑ (srel (Base.M-mul x y))) = begin
    dual ((M x • M y) ↑) ≈⟨ cong (refl' (aux-dual-Mx↑ x)) (refl' (aux-dual-Mx↑ y)) ⟩
    M x • M y ≈⟨ axiom (M-mul x y) ⟩
    M (x *' y) ≈⟨ sym (refl' (aux-dual-Mx↑ (x *' y))) ⟩
    dual (M (x *' y) ↑) ∎
  lemma-dual (cong↑ (srel (Base.semi-MS x))) = begin
    dual ((M x • S) ↑) ≈⟨ (cleft refl' (aux-dual-Mx↑ x)) ⟩
    M x • S ≈⟨ axiom (semi-MS x) ⟩
    S^ (x ^2) • M x ≈⟨ sym (cong (refl' (aux-dual-S^k↑ (toℕ (fromℕ< _)))) (refl' (aux-dual-Mx↑ x))) ⟩
    dual ((S^ (x ^2) • M x) ↑) ∎
  lemma-dual (cong↑ (cong↑ (srel ())))

  -- A proof principle for duality.
  by-duality : ∀ {w u} → w ≈ u → dual w ≈ dual u
  by-duality PB.refl = refl
  by-duality (PB.sym eq) = sym (by-duality eq)
  by-duality (PB.trans eq eq₁) = trans (by-duality eq) (by-duality eq₁)
  by-duality (PB.cong eq eq₁) = cong (by-duality eq) (by-duality eq₁)
  by-duality PB.assoc = assoc
  by-duality PB.left-unit = left-unit
  by-duality PB.right-unit = right-unit
  by-duality (PB.axiom x) = lemma-dual x


  -- A proof principle for duality.
  by-duality' : ∀ {w u w' u'} → w ≈ u → dual w ≈ w' → dual u ≈ u' → w' ≈ u'
  by-duality' eq eqw equ = trans (sym eqw) (trans (by-duality eq) equ)
