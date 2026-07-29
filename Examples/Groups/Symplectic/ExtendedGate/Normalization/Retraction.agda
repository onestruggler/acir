{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR


open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe
open import Data.Sum using ([_,_] ; [_,_]′)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥)

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



module Examples.Groups.Symplectic.ExtendedGate.Normalization.Retraction (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where





open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Lemmas-2Qupit p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.NF1 p-2 p-prime
open Lemmas-2Q 2
open Symplectic-Derived-Gen
open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Properties p-2 p-prime
open Normal-Form1
open import Examples.Groups.Symplectic.Normalization.NF p-2 p-prime

private
  variable
    n : ℕ

push-LM1 : ML 1 -> Gen 1 -> Word (Gen 0) × ML 1
push-LM1 : ML 1 -> Gen 1 -> Word (Gen 0) × ML 1


retraction : ∀ {n} -> NF n -> Word (Gen n)
retraction {₀} tt = ε
retraction {₁} (nf0 , m , l) = {!!}
retraction {₂₊ n} nf = {!!}
