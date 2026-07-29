{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS  --call-by-name #-}
{-# OPTIONS --termination-depth=4 #-}

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq


open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
open import Data.Bool hiding (_<_ ; _≤_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Vec as V
open import Data.Fin hiding (_+_ ; _-_ ; _≤_ ; _<_)

open import Data.Maybe
open import Data.Sum using (inj₁ ; inj₂ ; [_,_] ; [_,_]′)
open import Data.Unit using (tt)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)


open import Data.Fin using (toℕ)
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting using ()
open import Data.Nat.Primality



module Examples.Groups.Symplectic.Lemmas.Completeness (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

private
  variable
    n : ℕ
    




open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Cosets p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open import Examples.Groups.Symplectic.NF1-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime

open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Properties p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Soundness p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)
open import Examples.Groups.Symplectic.NF2-Sym p-2 p-prime
open LM2


open import Zp.ModularArithmetic
open import Examples.Groups.Symplectic.ExtendedGate.Lemmas-2Qupit p-2 p-prime
open import Examples.Groups.Symplectic.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2

open import Examples.Groups.Symplectic.ExtendedGate.NF1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym4 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym5 p-2 p-prime hiding (module L0)

open import Examples.Groups.Symplectic.Lemmas.Lemma-Comm-n p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Completeness1-Sym p-2 p-prime renaming (module Completeness to Cp1)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open Lemmas-Sym
open Duality

open import Examples.Groups.Symplectic.Lemmas.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()
open import Examples.Groups.Symplectic.Lemmas.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to CP2) using ()
open import Examples.Groups.Symplectic.Lemmas.Lemmas4-Sym p-2 p-prime


lemma-coset-update : let open PB ((₁₊ n) QRel,_===_) in

  ∀ (lm : ML (₁₊ n)) (g : (Gen (₁₊ n))) ->
  -------------------------------------------------------
  ∃ \ lm' -> ∃ \ w -> [ lm ]ᵐˡ • [ g ]ʷ ≈ w ↑ • [ lm' ]ᵐˡ

lemma-coset-update {n@0} lm g@H-gen = lm' , ε , claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  
  cp1 = CP1.Lemma-single-qupit-completeness {0} lm g  _
  lm' = cp1 .proj₁
  claim : [ lm ]ᵐˡ • [ H-gen ]ʷ ≈ (ε ↑) • [ lm' ]ᵐˡ
  claim = begin
    [ lm ]ᵐˡ • [ H-gen ]ʷ ≈⟨ cp1 .proj₂ ⟩
    [ lm' ]ᵐˡ ≈⟨ sym left-unit ⟩
    (ε ↑) • [ lm' ]ᵐˡ ∎
  
lemma-coset-update {n@0} lm g@S-gen = lm' , ε , claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  
  cp1 = CP1.Lemma-single-qupit-completeness {0} lm g  _
  lm' = cp1 .proj₁
  claim : [ lm ]ᵐˡ • [ S-gen ]ʷ ≈ (ε ↑) • [ lm' ]ᵐˡ
  claim = begin
    [ lm ]ᵐˡ • [ S-gen ]ʷ ≈⟨ cp1 .proj₂ ⟩
    [ lm' ]ᵐˡ ≈⟨ sym left-unit ⟩
    (ε ↑) • [ lm' ]ᵐˡ ∎

lemma-coset-update {n@1} lm g = CP2.Lemma-two-qupit-completeness lm g
lemma-coset-update {n@2} lm@(inj₂ (d , lm↑)) (g ↥) = lm' , w ↑ , claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  
  ih = lemma-coset-update lm↑ g
  lm↑' = ih .proj₁
  lm' = inj₂ (d , lm↑')
  w = ih .proj₂ .proj₁
  claim : [ lm ]ᵐˡ • [ g ↥ ]ʷ ≈ (w ↑ ↑) • [ lm' ]ᵐˡ
  claim = begin
    [ lm ]ᵐˡ • [ g ↥ ]ʷ ≈⟨ assoc ⟩
    [ d ]ᵈ • [ lm↑ ]ᵐˡ ↑ • [ g ↥ ]ʷ ≈⟨ refl ⟩
    [ d ]ᵈ • [ lm↑ ]ᵐˡ ↑ • [ g ]ʷ ↑ ≈⟨ (cright lemma-cong↑ _ _ (ih .proj₂ .proj₂)) ⟩
    [ d ]ᵈ • w ↑ ↑ • [ lm↑' ]ᵐˡ ↑ ≈⟨ sym assoc ⟩
    ([ d ]ᵈ • w ↑ ↑) • [ lm↑' ]ᵐˡ ↑ ≈⟨ (cleft comm-dbox-w↑↑ d w) ⟩
    (w ↑ ↑ • [ d ]ᵈ) • [ lm↑' ]ᵐˡ ↑ ≈⟨ assoc ⟩
    w ↑ ↑ • [ d ]ᵈ • [ lm↑' ]ᵐˡ ↑ ∎

lemma-coset-update {n@2} (inj₁ x) g = {!!}
lemma-coset-update {n@2} lm@(inj₂ (d@(₀ , b) , lm↑)) g@S-gen = lm' , w , claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

  lm' = lm
  w = S
  claim : [ lm ]ᵐˡ • [ g ]ʷ ≈ (S ↑) • [ lm' ]ᵐˡ
  claim = begin
    ([ d ]ᵈ • [ lm↑ ]ᵐˡ ↑) • [ g ]ʷ ≈⟨ assoc ⟩
    [ d ]ᵈ • [ lm↑ ]ᵐˡ ↑ • [ g ]ʷ ≈⟨ (cright sym (lemma-comm-S-w↑ [ lm↑ ]ᵐˡ)) ⟩
    [ d ]ᵈ • [ g ]ʷ • [ lm↑ ]ᵐˡ ↑ ≈⟨ sym assoc ⟩
    ([ d ]ᵈ • [ g ]ʷ) • [ lm↑ ]ᵐˡ ↑ ≈⟨ (cleft assoc) ⟩
    (Ex • CZ^ (- b) • [ g ]ʷ) • [ lm↑ ]ᵐˡ ↑ ≈⟨ (cleft cright comm⇒pow-comm (toℕ (- b)) 1 (axiom comm-CZ-S↓)) ⟩
    (Ex • [ g ]ʷ • CZ^ (- b)) • [ lm↑ ]ᵐˡ ↑ ≈⟨ sym (cong assoc refl) ⟩
    ((Ex • [ g ]ʷ) • CZ^ (- b)) • [ lm↑ ]ᵐˡ ↑ ≈⟨ (cleft cleft sym lemma-comm-Ex-S) ⟩
    ((S ↑ • Ex) • CZ^ (- b)) • [ lm↑ ]ᵐˡ ↑ ≈⟨ trans (cong assoc refl) assoc ⟩
    (S ↑) • [ lm' ]ᵐˡ ∎

lemma-coset-update {n@2} lm@(inj₂ (d@(a@(₁₊ _) , b) , lm↑)) g@S-gen = {!!}
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

  lm' = lm
  w = S
  claim : [ lm ]ᵐˡ • [ g ]ʷ ≈ (S ↑) • [ lm' ]ᵐˡ
  claim = begin
    ([ d ]ᵈ • [ lm↑ ]ᵐˡ ↑) • [ g ]ʷ ≈⟨ assoc ⟩
    [ d ]ᵈ • [ lm↑ ]ᵐˡ ↑ • [ g ]ʷ ≈⟨ (cright sym (lemma-comm-S-w↑ [ lm↑ ]ᵐˡ)) ⟩
    [ d ]ᵈ • [ g ]ʷ • [ lm↑ ]ᵐˡ ↑ ≈⟨ sym assoc ⟩
    ([ d ]ᵈ • [ g ]ʷ) • [ lm↑ ]ᵐˡ ↑ ≈⟨ (cleft {!!}) ⟩
    (Ex • CZ^ (- b) • [ g ]ʷ) • [ lm↑ ]ᵐˡ ↑ ≈⟨ (cleft cright comm⇒pow-comm (toℕ (- b)) 1 (axiom comm-CZ-S↓)) ⟩
    (Ex • [ g ]ʷ • CZ^ (- b)) • [ lm↑ ]ᵐˡ ↑ ≈⟨ sym (cong assoc refl) ⟩
    ((Ex • [ g ]ʷ) • CZ^ (- b)) • [ lm↑ ]ᵐˡ ↑ ≈⟨ (cleft cleft sym lemma-comm-Ex-S) ⟩
    ((S ↑ • Ex) • CZ^ (- b)) • [ lm↑ ]ᵐˡ ↑ ≈⟨ trans (cong assoc refl) {!!} ⟩
    (S ↑) • [ lm' ]ᵐˡ ∎

lemma-coset-update {n@2} lm@(inj₂ (d@(₀ , b@(₁₊ _)) , lm↑)) g@H-gen = lm' , w , claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas0 n
  open Pattern-Assoc

  b* : ℤ* ₚ
  b* = (b , λ ())

  b⁻¹ : ℤ* ₚ
  b⁻¹ = b* ⁻¹

  lm' : ML 3
  lm' = inj₂ (((b , ₀)) , lm↑)
  w = ZM b*
  claim : [ lm ]ᵐˡ • [ g ]ʷ ≈ ZM b* ↑ • [ lm' ]ᵐˡ
  claim = begin
    ([ d ]ᵈ • [ lm↑ ]ᵐˡ ↑) • H ≈⟨ assoc ⟩
    [ d ]ᵈ • [ lm↑ ]ᵐˡ ↑ • H ≈⟨ (cright sym (lemma-comm-H-w↑ [ lm↑ ]ᵐˡ)) ⟩
    [ d ]ᵈ • H • [ lm↑ ]ᵐˡ ↑ ≈⟨ sym assoc ⟩
    ([ d ]ᵈ • H) • [ lm↑ ]ᵐˡ ↑ ≈⟨ (cleft assoc) ⟩
    (Ex • CZ^ (- b) • H) • [ lm↑ ]ᵐˡ ↑ ≈⟨ (cleft cright cleft sym right-unit) ⟩
    (Ex • (CZ^ (- b) • ε) • H) • [ lm↑ ]ᵐˡ ↑ ≈⟨ (cleft cright cleft (cright sym (aux-M-mul b*))) ⟩
    (Ex • (CZ^ (- b) • ZM b* • ZM b⁻¹ ) • H) • [ lm↑ ]ᵐˡ ↑ ≈⟨ (cleft cright cleft sym assoc) ⟩
    (Ex • ((CZ^ (- b) • ZM b*) • ZM b⁻¹ ) • H) • [ lm↑ ]ᵐˡ ↑ ≈⟨ (cleft cright cleft (cleft {!lemma-CZ^kM!})) ⟩
    (Ex • ((ZM b* • CZ^ (- b * b⁻¹ ^1)) • ZM b⁻¹ ) • H) • [ lm↑ ]ᵐˡ ↑ ≡⟨ Eq.cong (\ xx -> (Ex • ((ZM b* • CZ^ xx) • ZM b⁻¹ ) • H) • [ lm↑ ]ᵐˡ ↑) aux2 ⟩
    (Ex • ((ZM b* • CZ^ (- ₁)) • ZM b⁻¹ ) • H) • [ lm↑ ]ᵐˡ ↑ ≈⟨ by-passoc ((□ • (□ ^ 2 • □) • □) • □ ) (□ ^ 2 • □ • □ ^ 2 • □) auto ⟩
    (Ex • ZM b*) • CZ^ (- ₁) • (ZM b⁻¹ • H) • [ lm↑ ]ᵐˡ ↑ ≈⟨ (cleft {!lemma-Ex-M!}) ⟩
    (ZM b* ↑ • Ex) • CZ^ (- ₁) • (ZM b⁻¹ • H) • [ lm↑ ]ᵐˡ ↑ ≈⟨ by-passoc  (□ ^ 2 • □ • □ ^ 2 • □) (□ • (□ ^ 2 • □ ^ 2) • □) auto ⟩
    ZM b* ↑ • ((Ex • CZ^ (- ₁)) • (ZM b⁻¹ • H)) • [ lm↑ ]ᵐˡ ↑ ≈⟨ (cright cleft cright  sym (lemma-Aa0 b*)) ⟩
    ZM b* ↑ • ((Ex • CZ^ (- ₁)) • ([ (b , ₀) , aux-a≠0⇒ab≠0 (b) (λ ()) ]ᵃ)) • [ lm↑ ]ᵐˡ ↑ ≈⟨ (cright  (cleft refl)) ⟩
    ZM b* ↑ • [ lm' ]ᵐˡ ∎
    where
    aux2 : - b * b⁻¹ ^1 ≡ - ₁
    aux2 = Eq.trans (Eq.sym (-‿distribˡ-* b (b⁻¹ ^1))) (Eq.cong -_ (lemma-⁻¹ʳ (b) {{nztoℕ {y = b} {neq0 = λ ()} }}))

lemma-coset-update {n@2} lm@(inj₂ (d@(₀ , b@₀) , lm↑)) g@H-gen = lm' , w , claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas0 n
  open Pattern-Assoc

  lm' : ML 3
  lm' = inj₂ (((₀ , ₀)) , lm↑)
  w = H
  claim : [ lm ]ᵐˡ • [ g ]ʷ ≈ w ↑ • [ lm' ]ᵐˡ
  claim = begin
    [ lm ]ᵐˡ • H ≈⟨ refl ⟩
    ((Ex • CZ^ (- ₀)) • [ lm↑ ]ᵐˡ ↑) • H ≡⟨ Eq.cong (\ xx -> ((Ex • CZ^ xx) • [ lm↑ ]ᵐˡ ↑) • H) -0#≈0# ⟩
    ((Ex • CZ^ (₀)) • [ lm↑ ]ᵐˡ ↑) • H ≈⟨ cong (cong right-unit refl) refl ⟩
    ((Ex) • [ lm↑ ]ᵐˡ ↑) • H ≈⟨ assoc ⟩
    Ex • [ lm↑ ]ᵐˡ ↑ • H ≈⟨ (cright sym (lemma-comm-H-w↑ [ lm↑ ]ᵐˡ)) ⟩
    Ex • H • [ lm↑ ]ᵐˡ ↑ ≈⟨ sym assoc ⟩
    (Ex • H) • [ lm↑ ]ᵐˡ ↑ ≈⟨ (cleft {!-0#≈0#!}) ⟩
    (H ↑ • Ex) • [ lm↑ ]ᵐˡ ↑ ≈⟨ assoc ⟩
    H ↑ • Ex • [ lm↑ ]ᵐˡ ↑ ≈⟨ (cright cleft sym right-unit) ⟩
    H ↑ • (Ex • CZ^ ₀) • [ lm↑ ]ᵐˡ ↑ ≡⟨ Eq.cong (\ xx -> H ↑ • (Ex • CZ^ xx) • [ lm↑ ]ᵐˡ ↑) (Eq.sym -0#≈0#) ⟩
    H ↑ • (Ex • CZ^ (- ₀)) • [ lm↑ ]ᵐˡ ↑ ≈⟨ refl ⟩
    w ↑ • [ lm' ]ᵐˡ ∎
