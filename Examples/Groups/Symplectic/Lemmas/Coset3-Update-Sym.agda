{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS  --call-by-name #-}
--{-# OPTIONS --termination-depth=2 #-}

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR


open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_,_ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ;  _≟_)
open import Agda.Builtin.Nat using (_-_)
open import Data.Bool hiding (_<_ ; _≤_ ; _≟_)
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
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)


open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_] ; inspect)
open import Data.Nat.Primality



module Examples.Groups.Symplectic.Lemmas.Coset3-Update-Sym (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Lemmas-2Qupit p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2
open Symplectic
open Lemmas-Sym
open import Examples.Groups.Symplectic.ExtendedGate.NF1-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym4 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym5 p-2 p-prime hiding (module L0)
open import Examples.Groups.Symplectic.Cosets p-2 p-prime

open import Examples.Groups.Symplectic.Lemmas.Lemma-Comm p-2 p-prime 0
open import Examples.Groups.Symplectic.Lemmas.Completeness1-Sym p-2 p-prime renaming (module Completeness to Cp1)
open import Examples.Groups.Symplectic.Lemmas.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to Cp2)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c

open LM2
open import Examples.Groups.Symplectic.Lemmas.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()


module Completeness where

  open PB (3 QRel,_===_)
  open PP (3 QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Sym0-Rewriting 1

  open import Examples.Groups.Symplectic.Proofs.P1 p-2 p-prime
  open import Examples.Groups.Symplectic.Proofs.P2 p-2 p-prime
  open import Examples.Groups.Symplectic.Proofs.P3 p-2 p-prime
  open import Examples.Groups.Symplectic.Proofs.P4 p-2 p-prime
  open import Examples.Groups.Symplectic.Proofs.P5 p-2 p-prime
  open import Examples.Groups.Symplectic.Proofs.P6 p-2 p-prime
  open import Examples.Groups.Symplectic.Proofs.P7 p-2 p-prime hiding (module L0)
  open import Examples.Groups.Symplectic.Proofs.P8 p-2 p-prime
  open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime as TQ
  open import Examples.Groups.Symplectic.Lemmas.Lemma-Postfix p-2 p-prime
  open import Examples.Groups.Symplectic.Lemmas.Derived p-2 p-prime
  open import Examples.Groups.Symplectic.Lemmas.Derived2 p-2 p-prime
--  open import Examples.Groups.Symplectic.ExtendedGate.NF1-Sym p-2 p-prime as NF1
--  open NF1.Normal-Form1 using ()
  
  open TQ.Lemmas-2Q 0
  open Duality
  import Examples.Groups.Symplectic.Lemmas.Duality p-2 p-prime as ND
  open Lemmas0 1
  module L0 = Lemmas0 0
  open import Algebra.Properties.Ring (+-*-ring p-2)
  open import Zp.Mod-Lemmas p-2 p-prime

  Lemma-three-qupit-completeness :

    ∀ (lm : Cosets3) (g :(Gen 3)) ->
    -----------------------------------------------------
    ∃ \ lm' -> ∃ \ w -> ⟦ lm ⟧₃ • [ g ]ʷ ≈ w ↑ • ⟦ lm' ⟧₃

  Lemma-three-qupit-completeness (case-I x x₁ x₂) H-gen = {!!}
  Lemma-three-qupit-completeness (case-I x x₁ x₂) S-gen = {!!}
  Lemma-three-qupit-completeness (case-I x x₁ x₂) CZ-gen = {!!}
  Lemma-three-qupit-completeness (case-I x x₁ x₂) (g ↥) = {!!}
  Lemma-three-qupit-completeness (case-II x x₁ x₂ x₃ x₄) H-gen = {!!}
  Lemma-three-qupit-completeness (case-II x x₁ x₂ x₃ x₄) S-gen = {!!}
  Lemma-three-qupit-completeness (case-II x x₁ x₂ x₃ x₄) CZ-gen = {!!}
  Lemma-three-qupit-completeness (case-II x x₁ x₂ x₃ x₄) (g ↥) = {!!}
