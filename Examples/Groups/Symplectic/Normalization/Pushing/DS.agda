{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS  --call-by-name #-}
{-# OPTIONS --termination-depth=4 #-}

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
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Vec as V
open import Data.Fin hiding (_+_ ; _-_ ; _≤_ ; _<_)

open import Data.Maybe
open import Data.Sum using ([_,_] ; [_,_]′)
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



module Examples.Groups.Symplectic.Normalization.Pushing.DS (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

private
  variable
    n : ℕ
    




open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Cosets p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open import Examples.Groups.Symplectic.ExtendedGate.NF1-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime

open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Action.Properties p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Soundness p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)
open import Examples.Groups.Symplectic.ExtendedGate.NF2-Sym p-2 p-prime
open LM2


open import Zp.ModularArithmetic
open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2

open import Examples.Groups.Symplectic.ExtendedGate.NF1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym4 p-2 p-prime
--open import Examples.Groups.Symplectic.Lemmas.Ex-Sym5 p-2 p-prime hiding (module L0)
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2n p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n p-2 p-prime

open import Examples.Groups.Symplectic.Lemmas.Lemma-Comm-n p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Completeness1-Sym p-2 p-prime renaming (module Completeness to Cp1)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open Lemmas-Sym
open Duality

open import Examples.Groups.Symplectic.Lemmas.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()
--open import Examples.Groups.Symplectic.Lemmas.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to CP2) using ()
open import Examples.Groups.Symplectic.Lemmas.Lemmas4-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.DH p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.AS p-2 p-prime



dir-of-DS : D -> Word (Gen (₁₊ n))
dir-of-DS (₀ , b) = S
dir-of-DS (₁₊ _ , _) = ε

d-of-DS : D -> D
d-of-DS (₀ , b) = ₀ , b
d-of-DS (a@(₁₊ _) , b) = a , b + - a

aux-DS : let open PB ((₂₊ n) QRel,_===_) in

  ∀ d ->
  let
  d' = d-of-DS d
  w = dir-of-DS d
  in
  [ d ]ᵈ • S ≈ w ↑ • [ d' ]ᵈ

aux-DS {n} d@(a@₀ , b) = claim
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

  claim : [ d ]ᵈ • S ≈ S ↑ • [ d ]ᵈ
  claim = begin
    ([ d ]ᵈ • S) ≈⟨ assoc ⟩
    (Ex • CZ^ (- b) • S) ≈⟨ (cright comm⇒pow-comm (toℕ (- b)) 1 (axiom comm-CZ-S↓)) ⟩
    Ex • S • CZ^ (- b) ≈⟨ sym assoc ⟩
    (Ex • S) • CZ^ (- b) ≈⟨ (cleft lemma-Ex-S) ⟩
    (S ↑ • Ex) • CZ^ (- b) ≈⟨ assoc ⟩
    S ↑ • [ d ]ᵈ ∎
    

aux-DS {n} d@(a@(₁₊ _) , b) = claim
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  aux : -b/a + ₁ ≡ - (b + - a) * a⁻¹
  aux = Eq.sym ( begin
    - (b + - a) * a⁻¹ ≡⟨ Eq.cong (_* a⁻¹) (Eq.sym (-‿+-comm b (- a))) ⟩
    (- b + - - a) * a⁻¹ ≡⟨ Eq.cong (\ xx -> (- b + xx) * a⁻¹) (-‿involutive a) ⟩
    (- b + a) * a⁻¹ ≡⟨ *-distribʳ-+ a⁻¹ (- b) a ⟩
    - b * a⁻¹ + a * a⁻¹ ≡⟨ Eq.cong (- b * a⁻¹ +_) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = λ ()}}}) ⟩
    - b * a⁻¹ + ₁ ≡⟨ auto ⟩
    -b/a + ₁ ∎
    )
    where
    open ≡-Reasoning

  
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas0 (₁₊ n)
  open Pattern-Assoc

  w = S
  d' = (a , b + - a)
  
  claim : [ d ]ᵈ • S ≈ (ε ↑) • [ d' ]ᵈ
  claim = begin
    ((Ex • CZ^ (- a) • H • S^ -b/a) • S) ≈⟨ by-passoc (□ ^ 4 • □) (□ ^ 5) auto ⟩
    Ex • CZ^ (- a) • H • S^ -b/a • S ≈⟨ (cright cright cright lemma-S^k+l -b/a ₁) ⟩
    Ex • CZ^ (- a) • H • S^ (-b/a + ₁) ≈⟨ (cright cright cright refl' (Eq.cong S^ aux)) ⟩
    Ex • CZ^ (- a) • H • S^ (- (b + - a) * a⁻¹) ≈⟨ refl ⟩
    ([ (a , (b + - a)) ]ᵈ) ≈⟨ sym left-unit ⟩
    ε • ([ (a , (b + - a)) ]ᵈ)  ∎



aux-DS↑ : let open PB ((₂₊ n) QRel,_===_) in

  ∀ d -> [ d ]ᵈ • S ↑ ≈ S • [ d ]ᵈ

aux-DS↑ {n} d@(a@₀ , b) = begin
  ([ d ]ᵈ • S ↑) ≈⟨ assoc ⟩
  (Ex • CZ^ (- b) • S ↑) ≈⟨ (cright comm⇒pow-comm (toℕ (- b)) 1 (axiom comm-CZ-S↑)) ⟩
  Ex • S ↑ • CZ^ (- b) ≈⟨ sym assoc ⟩
  (Ex • S ↑) • CZ^ (- b) ≈⟨ (cleft lemma-Ex-S↑-n) ⟩
  (S • Ex) • CZ^ (- b) ≈⟨ assoc ⟩
  S • [ d ]ᵈ ∎
  where
  
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas0 (₁₊ n)
  open Pattern-Assoc
  
aux-DS↑ {n} d@(a@(₁₊ _) , b) = begin
  [ d ]ᵈ • S ↑ ≈⟨ refl ⟩
  (Ex • CZ^ (- a) • H • S^ -b/a) • S ↑ ≈⟨ by-passoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (Ex • CZ^ (- a)) • (H • S^ -b/a) • S ↑ ≈⟨ (cright comm-hs-w↑ -b/a S) ⟩
  (Ex • CZ^ (- a)) • S ↑ • H • S^ -b/a ≈⟨ by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  Ex • (CZ^ (- a) • S ↑) • H • S^ -b/a ≈⟨ (cright cleft comm⇒pow-comm (toℕ (- a)) 1 (axiom comm-CZ-S↑)) ⟩
  Ex • (S ↑ • CZ^ (- a)) • H • S^ -b/a ≈⟨ sym (by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ) ⟩
  (Ex • S ↑) • CZ^ (- a) • H • S^ -b/a ≈⟨ (cleft lemma-Ex-Sᵏ↑ 1) ⟩
  (S • Ex) • CZ^ (- a) • H • S^ -b/a ≈⟨ assoc ⟩
  S • [ d ]ᵈ ∎
  where
  
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas0 (₁₊ n)
  open Pattern-Assoc
  
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
