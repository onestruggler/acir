{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq


open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_,_)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
import Data.Nat as Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe
open import Data.Sum using ([_,_] ; [_,_]′)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)


import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_])
open import Data.Nat.Primality



module Examples.Groups.Symplectic.Lemmas.GroupLike (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where





open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime


private
  variable
    n : ℕ


open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2n p-2 p-prime
open Symplectic
open Lemmas-Sym

grouplike : Grouplike (n QRel,_===_)
grouplike {₁₊ n} (H-gen) = (H ) ^ 3 , claim
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  claim : (H ) ^ 3 • H ≈ ε
  claim = begin
    (H) ^ 3 • H ≈⟨ by-assoc auto ⟩
    (H) ^ 4 ≈⟨ axiom order-H ⟩
    ε ∎

grouplike {₁₊ n} (S-gen) = (S) ^ p-1 ,  claim
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  claim : (S) ^ p-1 • S ≈ ε
  claim = begin
    (S) ^ p-1 • S ≈⟨ sym (^-+ (S) p-1 1) ⟩
    (S) ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (S ^_) ( NP.+-comm p-1 1) ⟩
    (S ^ p) ≈⟨ (axiom order-S) ⟩
    (ε) ∎

grouplike {₂₊ n} (CZ-gen) = (CZ) ^ p-1 ,  claim
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  claim : (CZ) ^ p-1 • CZ ≈ ε
  claim = begin
    (CZ) ^ p-1 • CZ ≈⟨ sym (^-+ (CZ) p-1 1) ⟩
    (CZ) ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (CZ ^_) ( NP.+-comm p-1 1) ⟩
    (CZ ^ p) ≈⟨ (axiom order-CZ) ⟩
    (ε) ∎

grouplike {₂₊ n} (EX-gen) = EX ,  claim
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  claim : (EX) • EX ≈ ε
  claim = {!!}

grouplike {₂₊ n} (g ↥) with grouplike g
... | ig , prf = (ig ↑) , lemma-cong↑ (ig • [ g ]ʷ) ε prf
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
