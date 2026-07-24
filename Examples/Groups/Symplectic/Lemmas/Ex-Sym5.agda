{-# OPTIONS --cubical-compatible --safe #-}
--{-# OPTIONS --termination-depth=2 #-}

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq


open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_,_ ; proj₁ ; proj₂)
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



module Examples.Groups.Symplectic.Lemmas.Ex-Sym5 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where





open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime
open import Examples.Groups.Symplectic.NF2-Sym p-2 p-prime
open Lemmas-2Q 0
open Symplectic
open import Examples.Groups.Symplectic.NF1-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym4 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Rewriting p-2 p-prime
open Rewriting-Ex

open import Examples.Groups.Symplectic.Lemmas.Lemma-Comm p-2 p-prime 0
open import Examples.Groups.Symplectic.Lemmas.Lemma-Postfix p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Duality p-2 p-prime hiding (module L0)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c

open LM2
open import Examples.Groups.Symplectic.Lemmas.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()

private
  variable
    n : ℕ

open Symplectic
open Lemmas-Sym
open Symplectic-GroupLike

open import Data.Nat.DivMod
open import Data.Fin.Properties
open Duality







open import Algebra.Properties.Ring (+-*-ring p-2)
open PB (₂ QRel,_===_)
open PP (₂ QRel,_===_)
open SR word-setoid
open Pattern-Assoc
open Lemmas0 1
open Commuting-Symplectic 0
open Sym0-Rewriting 1
open Basis-Change _ ((₂₊ 0) QRel,_===_) grouplike
import Examples.Groups.Symplectic.Lemmas.Duality p-2 p-prime as ND

open import Examples.Groups.Symplectic.Cosets p-2 p-prime
{-

open import Examples.Groups.Symplectic.Proofs-bak.P1 p-2 p-prime
open import Examples.Groups.Symplectic.Proofs-bak.P2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime as TQ

open Duality
open Lemmas0 1
module L0 = Lemmas0 0


step-|-CZa : ∀ m s' m' ->
  let
    aa = ((m ⁻¹) .proj₁ + m' .proj₁)
  in aa ≡ ₀ -> 
  ⟦ case-| (m , ε) (s' , m' , ε) ⟧₂ • CZ ≈ (⟦ m ⟧ₘ ↑) • ⟦ case-nf1 (s' , m' , ε) ⟧₂
  
step-|-CZa m s' m' eq = claim
  where
  claim : ⟦ case-| (m , ε) (s' , m' , ε) ⟧₂ • CZ ≈ (⟦ m ⟧ₘ ↑) • ⟦ case-nf1 (s' , m' , ε) ⟧₂
  claim  = begin
    ⟦ case-| (m , ε) (s' , m' , ε) ⟧₂ • CZ ≈⟨ trans assoc (cong refl assoc) ⟩
    CZ • ⟦ (m , ε) ⟧ₘ₊ ↑ • ⟦ (s' , m' , ε) ⟧₁ • CZ ≈⟨ (cright cong right-unit (cong (cong refl right-unit) refl)) ⟩
    CZ • ⟦ m ⟧ₘ ↑ • (S^ s' • ⟦ m' ⟧ₘ) • CZ ≈⟨ (cright by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    CZ • (⟦ m ⟧ₘ ↑ • S^ s') • ⟦ m' ⟧ₘ • CZ ≈⟨ (cright cleft sym (lemma-comm-Sᵏ-w↑ (toℕ s') ⟦ m ⟧ₘ)) ⟩
    CZ • (S^ s' • ⟦ m ⟧ₘ ↑) • ⟦ m' ⟧ₘ • CZ ≈⟨ by-passoc (□ • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 3) auto ⟩
    (CZ • S^ s') • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ • CZ ≈⟨ (cleft comm⇒pow-comm 1 (toℕ s') (axiom comm-CZ-S↓)) ⟩
    (S^ s' • CZ) • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ • CZ ≈⟨ assoc ⟩
    S^ s' • CZ • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ • CZ ≈⟨ ( cright  lemma-|MM| m m') ⟩
    S^ s' • ⟦ m ⟧ₘ ↑ • (CZ^ ((m ⁻¹) .proj₁ + m' .proj₁)) • ⟦ m' ⟧ₘ ≈⟨ (cright cright cleft refl' (Eq.cong CZ^ eq)) ⟩
    S^ s' • ⟦ m ⟧ₘ ↑ • (CZ^ ₀) • ⟦ m' ⟧ₘ ≈⟨ cong refl (cong refl left-unit) ⟩
    S^ s' • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ ≈⟨ sym assoc ⟩
    (S^ s' • ⟦ m ⟧ₘ ↑) • ⟦ m' ⟧ₘ ≈⟨ (cleft lemma-comm-Sᵏ-w↑ (toℕ s') ⟦ m ⟧ₘ) ⟩
    (⟦ m ⟧ₘ ↑ • S^ s') • ⟦ m' ⟧ₘ ≈⟨ assoc ⟩
    ⟦ m ⟧ₘ ↑ • S^ s' • ⟦ m' ⟧ₘ ≈⟨ (cright cright  sym right-unit) ⟩
    ⟦ m ⟧ₘ ↑ • S^ s' • ⟦ m' ⟧ₘ • ε ≈⟨ refl ⟩
    ⟦ m ⟧ₘ ↑ • ⟦ (s' , m' , ε) ⟧₁ ∎

step-|-CZb : ∀ m s' m' ->
  let
    aa = ((m ⁻¹) .proj₁ + m' .proj₁)
  in (neq : aa ≢ ₀) -> 
  ⟦ case-| (m , ε) (s' , m' , ε) ⟧₂ • CZ ≈ (⟦ m ⟧ₘ • M (aa , neq)) ↑ • ⟦ case-| ((aa , neq) ⁻¹ , ε) (s' , m' , ε) ⟧₂
  
step-|-CZb m s' m' neq = claim
  where
  aa = ((m ⁻¹) .proj₁ + m' .proj₁)
  
  claim : ⟦ case-| (m , ε) (s' , m' , ε) ⟧₂ • CZ ≈ (⟦ m ⟧ₘ • M (aa , neq)) ↑ • ⟦ case-| ((aa , neq) ⁻¹ , ε) (s' , m' , ε) ⟧₂
  claim = begin
    ⟦ case-| (m , ε) (s' , m' , ε) ⟧₂ • CZ ≈⟨ trans assoc (cong refl assoc) ⟩
    CZ • ⟦ (m , ε) ⟧ₘ₊ ↑ • ⟦ (s' , m' , ε) ⟧₁ • CZ ≈⟨ (cright cong right-unit (cong (cong refl right-unit) refl)) ⟩
    CZ • ⟦ m ⟧ₘ ↑ • (S^ s' • ⟦ m' ⟧ₘ) • CZ ≈⟨ (cright by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    CZ • (⟦ m ⟧ₘ ↑ • S^ s') • ⟦ m' ⟧ₘ • CZ ≈⟨ (cright cleft sym (lemma-comm-Sᵏ-w↑ (toℕ s') ⟦ m ⟧ₘ)) ⟩
    CZ • (S^ s' • ⟦ m ⟧ₘ ↑) • ⟦ m' ⟧ₘ • CZ ≈⟨ by-passoc (□ • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 3) auto ⟩
    (CZ • S^ s') • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ • CZ ≈⟨ (cleft comm⇒pow-comm 1 (toℕ s') (axiom comm-CZ-S↓)) ⟩
    (S^ s' • CZ) • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ • CZ ≈⟨ assoc ⟩
    S^ s' • CZ • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ • CZ ≈⟨ ( cright  lemma-|MM| m m') ⟩
    S^ s' • ⟦ m ⟧ₘ ↑ • (CZ^ ((m ⁻¹) .proj₁ + m' .proj₁)) • ⟦ m' ⟧ₘ ≈⟨ sym assoc ⟩
    (S^ s' • ⟦ m ⟧ₘ ↑) • (CZ^ ((m ⁻¹) .proj₁ + m' .proj₁)) • ⟦ m' ⟧ₘ ≈⟨ cong (lemma-comm-Sᵏ-w↑ (toℕ s') ⟦ m ⟧ₘ) (sym left-unit) ⟩
    (⟦ m ⟧ₘ ↑ • S^ s') • ε • (CZ^ ((m ⁻¹) .proj₁ + m' .proj₁)) • ⟦ m' ⟧ₘ ≈⟨ sym (cright cleft lemma-cong↑ _ _ (L0.aux-M-mul (aa , neq))) ⟩
    (⟦ m ⟧ₘ ↑ • S^ s') • (M (aa , neq) ↑ • M ((aa , neq) ⁻¹) ↑ ) • (CZ^ ((m ⁻¹) .proj₁ + m' .proj₁)) • ⟦ m' ⟧ₘ ≈⟨ (cright assoc) ⟩
    (⟦ m ⟧ₘ ↑ • S^ s') • M (aa , neq) ↑ • M ((aa , neq) ⁻¹) ↑  • (CZ^ ((m ⁻¹) .proj₁ + m' .proj₁)) • ⟦ m' ⟧ₘ ≈⟨ (cright cright sym assoc) ⟩
    (⟦ m ⟧ₘ ↑ • S^ s') • M (aa , neq) ↑ • (M ((aa , neq) ⁻¹) ↑  • CZ^ ((m ⁻¹) .proj₁ + m' .proj₁)) • ⟦ m' ⟧ₘ ≈⟨ (cright cright cleft lemma-M↑CZ^k (((aa , neq) ⁻¹) .proj₁) (((m ⁻¹) .proj₁ + m' .proj₁)) (((aa , neq) ⁻¹) .proj₂)) ⟩
    (⟦ m ⟧ₘ ↑ • S^ s') • M (aa , neq) ↑ • (CZ^ (((m ⁻¹) .proj₁ + m' .proj₁) * ((aa , neq) ⁻¹) .proj₁) • M ((aa , neq) ⁻¹) ↑) • ⟦ m' ⟧ₘ ≈⟨ assoc ⟩
    ⟦ m ⟧ₘ ↑ • S^ s' • M (aa , neq) ↑ • (CZ^ (((m ⁻¹) .proj₁ + m' .proj₁) * ((aa , neq) ⁻¹) .proj₁) • M ((aa , neq) ⁻¹) ↑) • ⟦ m' ⟧ₘ ≈⟨ (cright sym assoc) ⟩
    ⟦ m ⟧ₘ ↑ • (S^ s' • M (aa , neq) ↑) • (CZ^ (((m ⁻¹) .proj₁ + m' .proj₁) * ((aa , neq) ⁻¹) .proj₁) • M ((aa , neq) ⁻¹) ↑) • ⟦ m' ⟧ₘ ≈⟨ (cright cong (lemma-comm-Sᵏ-w↑ (toℕ s') (M (aa , neq))) (cleft (cleft refl' (Eq.cong CZ^ aux)))) ⟩
    ⟦ m ⟧ₘ ↑ • (M (aa , neq) ↑ • S^ s') • (CZ • M ((aa , neq) ⁻¹) ↑) • ⟦ m' ⟧ₘ ≈⟨ (cright assoc) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • S^ s' • (CZ • M ((aa , neq) ⁻¹) ↑) • ⟦ m' ⟧ₘ ≈⟨ (cright cright by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • (S^ s' • CZ) • M ((aa , neq) ⁻¹) ↑ • ⟦ m' ⟧ₘ ≈⟨ (cright cright cleft comm⇒pow-comm (toℕ s') 1 (sym (axiom comm-CZ-S↓))) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • (CZ • S^ s') • M ((aa , neq) ⁻¹) ↑ • ⟦ m' ⟧ₘ ≈⟨ (cright cright assoc) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • CZ • S^ s' • M ((aa , neq) ⁻¹) ↑ • ⟦ m' ⟧ₘ ≈⟨ (cright cright cright sym assoc) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • CZ • (S^ s' • M ((aa , neq) ⁻¹) ↑) • ⟦ m' ⟧ₘ ≈⟨ (cright cright cright cleft lemma-comm-Sᵏ-w↑ (toℕ s') (M ((aa , neq) ⁻¹))) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • CZ • (M ((aa , neq) ⁻¹) ↑ • S^ s') • ⟦ m' ⟧ₘ ≈⟨ (cright cright cright assoc) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • CZ • M ((aa , neq) ⁻¹) ↑ • S^ s' • ⟦ m' ⟧ₘ ≈⟨ (cright cright cright cright sym (cong refl right-unit)) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • CZ • (M ((aa , neq) ⁻¹) ↑) • S^ s' • ⟦ m' ⟧ₘ • ε ≈⟨ (cright cright cright cleft sym right-unit) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • CZ • (M ((aa , neq) ⁻¹) ↑ • ε) • S^ s' • ⟦ m' ⟧ₘ • ε ≈⟨ sym assoc ⟩
    (⟦ m ⟧ₘ • M (aa , neq)) ↑ • ⟦ case-| ((aa , neq) ⁻¹ , ε) (s' , m' , ε) ⟧₂ ∎
    where
    aux : (((m ⁻¹) .proj₁ + m' .proj₁) * ((aa , neq) ⁻¹) .proj₁) ≡ ₁
    aux = (lemma-⁻¹ʳ (aa) {{nztoℕ {y = aa} {neq0 = neq}}})



step-|-CZc : ∀ m s' m' ->
  let
    aa = ((m ⁻¹) .proj₁ + m' .proj₁)
  in (neq : aa ≢ ₀) -> 
  ⟦ case-| (m , ε) (s' , m' , ε) ⟧₂ • CZ ≈ (⟦ m ⟧ₘ • M (aa , neq)) ↑ • ⟦ case-| ((aa , neq) ⁻¹ , ε) (s' , m' , ε) ⟧₂
  
step-|-CZc m s' m' neq = claim
  where
  aa = ((m ⁻¹) .proj₁ + m' .proj₁)
  
  claim : ⟦ case-| (m , ε) (s' , m' , ε) ⟧₂ • CZ ≈ (⟦ m ⟧ₘ • M (aa , neq)) ↑ • ⟦ case-| ((aa , neq) ⁻¹ , ε) (s' , m' , ε) ⟧₂
  claim = begin
    ⟦ case-| (m , ε) (s' , m' , ε) ⟧₂ • CZ ≈⟨ trans assoc (cong refl assoc) ⟩
    CZ • ⟦ (m , ε) ⟧ₘ₊ ↑ • ⟦ (s' , m' , ε) ⟧₁ • CZ ≈⟨ (cright cong right-unit (cong (cong refl right-unit) refl)) ⟩
    CZ • ⟦ m ⟧ₘ ↑ • (S^ s' • ⟦ m' ⟧ₘ) • CZ ≈⟨ (cright by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    CZ • (⟦ m ⟧ₘ ↑ • S^ s') • ⟦ m' ⟧ₘ • CZ ≈⟨ (cright cleft sym (lemma-comm-Sᵏ-w↑ (toℕ s') ⟦ m ⟧ₘ)) ⟩
    CZ • (S^ s' • ⟦ m ⟧ₘ ↑) • ⟦ m' ⟧ₘ • CZ ≈⟨ by-passoc (□ • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 3) auto ⟩
    (CZ • S^ s') • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ • CZ ≈⟨ (cleft comm⇒pow-comm 1 (toℕ s') (axiom comm-CZ-S↓)) ⟩
    (S^ s' • CZ) • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ • CZ ≈⟨ assoc ⟩
    S^ s' • CZ • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ • CZ ≈⟨ ( cright  lemma-|MM| m m') ⟩
    S^ s' • ⟦ m ⟧ₘ ↑ • (CZ^ ((m ⁻¹) .proj₁ + m' .proj₁)) • ⟦ m' ⟧ₘ ≈⟨ sym assoc ⟩
    (S^ s' • ⟦ m ⟧ₘ ↑) • (CZ^ ((m ⁻¹) .proj₁ + m' .proj₁)) • ⟦ m' ⟧ₘ ≈⟨ cong (lemma-comm-Sᵏ-w↑ (toℕ s') ⟦ m ⟧ₘ) (sym left-unit) ⟩
    (⟦ m ⟧ₘ ↑ • S^ s') • ε • (CZ^ ((m ⁻¹) .proj₁ + m' .proj₁)) • ⟦ m' ⟧ₘ ≈⟨ sym (cright cleft lemma-cong↑ _ _ (L0.aux-M-mul (aa , neq))) ⟩
    (⟦ m ⟧ₘ ↑ • S^ s') • (M (aa , neq) ↑ • M ((aa , neq) ⁻¹) ↑ ) • (CZ^ ((m ⁻¹) .proj₁ + m' .proj₁)) • ⟦ m' ⟧ₘ ≈⟨ (cright assoc) ⟩
    (⟦ m ⟧ₘ ↑ • S^ s') • M (aa , neq) ↑ • M ((aa , neq) ⁻¹) ↑  • (CZ^ ((m ⁻¹) .proj₁ + m' .proj₁)) • ⟦ m' ⟧ₘ ≈⟨ (cright cright sym assoc) ⟩
    (⟦ m ⟧ₘ ↑ • S^ s') • M (aa , neq) ↑ • (M ((aa , neq) ⁻¹) ↑  • CZ^ ((m ⁻¹) .proj₁ + m' .proj₁)) • ⟦ m' ⟧ₘ ≈⟨ (cright cright cleft lemma-M↑CZ^k (((aa , neq) ⁻¹) .proj₁) (((m ⁻¹) .proj₁ + m' .proj₁)) (((aa , neq) ⁻¹) .proj₂)) ⟩
    (⟦ m ⟧ₘ ↑ • S^ s') • M (aa , neq) ↑ • (CZ^ (((m ⁻¹) .proj₁ + m' .proj₁) * ((aa , neq) ⁻¹) .proj₁) • M ((aa , neq) ⁻¹) ↑) • ⟦ m' ⟧ₘ ≈⟨ assoc ⟩
    ⟦ m ⟧ₘ ↑ • S^ s' • M (aa , neq) ↑ • (CZ^ (((m ⁻¹) .proj₁ + m' .proj₁) * ((aa , neq) ⁻¹) .proj₁) • M ((aa , neq) ⁻¹) ↑) • ⟦ m' ⟧ₘ ≈⟨ (cright sym assoc) ⟩
    ⟦ m ⟧ₘ ↑ • (S^ s' • M (aa , neq) ↑) • (CZ^ (((m ⁻¹) .proj₁ + m' .proj₁) * ((aa , neq) ⁻¹) .proj₁) • M ((aa , neq) ⁻¹) ↑) • ⟦ m' ⟧ₘ ≈⟨ (cright cong (lemma-comm-Sᵏ-w↑ (toℕ s') (M (aa , neq))) (cleft (cleft refl' (Eq.cong CZ^ aux)))) ⟩
    ⟦ m ⟧ₘ ↑ • (M (aa , neq) ↑ • S^ s') • (CZ • M ((aa , neq) ⁻¹) ↑) • ⟦ m' ⟧ₘ ≈⟨ (cright assoc) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • S^ s' • (CZ • M ((aa , neq) ⁻¹) ↑) • ⟦ m' ⟧ₘ ≈⟨ (cright cright by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • (S^ s' • CZ) • M ((aa , neq) ⁻¹) ↑ • ⟦ m' ⟧ₘ ≈⟨ (cright cright cleft comm⇒pow-comm (toℕ s') 1 (sym (axiom comm-CZ-S↓))) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • (CZ • S^ s') • M ((aa , neq) ⁻¹) ↑ • ⟦ m' ⟧ₘ ≈⟨ (cright cright assoc) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • CZ • S^ s' • M ((aa , neq) ⁻¹) ↑ • ⟦ m' ⟧ₘ ≈⟨ (cright cright cright sym assoc) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • CZ • (S^ s' • M ((aa , neq) ⁻¹) ↑) • ⟦ m' ⟧ₘ ≈⟨ (cright cright cright cleft lemma-comm-Sᵏ-w↑ (toℕ s') (M ((aa , neq) ⁻¹))) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • CZ • (M ((aa , neq) ⁻¹) ↑ • S^ s') • ⟦ m' ⟧ₘ ≈⟨ (cright cright cright assoc) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • CZ • M ((aa , neq) ⁻¹) ↑ • S^ s' • ⟦ m' ⟧ₘ ≈⟨ (cright cright cright cright sym (cong refl right-unit)) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • CZ • (M ((aa , neq) ⁻¹) ↑) • S^ s' • ⟦ m' ⟧ₘ • ε ≈⟨ (cright cright cright cleft sym right-unit) ⟩
    ⟦ m ⟧ₘ ↑ • M (aa , neq) ↑ • CZ • (M ((aa , neq) ⁻¹) ↑ • ε) • S^ s' • ⟦ m' ⟧ₘ • ε ≈⟨ sym assoc ⟩
    (⟦ m ⟧ₘ • M (aa , neq)) ↑ • ⟦ case-| ((aa , neq) ⁻¹ , ε) (s' , m' , ε) ⟧₂ ∎
    where
    aux : (((m ⁻¹) .proj₁ + m' .proj₁) * ((aa , neq) ⁻¹) .proj₁) ≡ ₁
    aux = (lemma-⁻¹ʳ (aa) {{nztoℕ {y = aa} {neq0 = neq}}})


-}
