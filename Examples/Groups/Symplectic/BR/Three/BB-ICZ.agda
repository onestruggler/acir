{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS  --call-by-name #-}
{-# OPTIONS --termination-depth=4 #-}

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR


open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_,_)
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


open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting using ()
open import Data.Nat.Primality



module Examples.Groups.Symplectic.BR.Three.BB-ICZ (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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

open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Properties p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Soundness p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)
open import Examples.Groups.Symplectic.ExtendedGate.NF2-Sym p-2 p-prime
open LM2


open import Zp.ModularArithmetic
open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym3 p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2

open import Examples.Groups.Symplectic.ExtendedGate.NF1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym4 p-2 p-prime hiding (lemma-Ex-S^ᵏ ; lemma-Ex-S^ᵏ↑)
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym5 p-2 p-prime hiding (module L0)
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2n p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym4n p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym4n2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym4n3 p-2 p-prime


open import Examples.Groups.Symplectic.Lemmas.Lemma-Comm-n p-2 p-prime 0
import Examples.Groups.Symplectic.Lemmas.Lemma-Comm-n p-2 p-prime 1 as LCn1
open import Examples.Groups.Symplectic.Lemmas.Completeness1-Sym p-2 p-prime renaming (module Completeness to Cp1)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open Lemmas-Sym
open Duality

open import Examples.Groups.Symplectic.Lemmas.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()
open import Examples.Groups.Symplectic.Lemmas.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to CP2) using ()
open import Examples.Groups.Symplectic.Lemmas.Lemmas4-Sym p-2 p-prime as L4
open import Examples.Groups.Symplectic.Lemmas.Lemmas-3Q p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.DH p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Duality p-2 p-prime
open import Examples.Groups.Symplectic.BR.Calculations p-2 p-prime
open import Examples.Groups.Symplectic.BR.Three.Lemmas p-2 p-prime
open import Examples.Groups.Symplectic.BR.Three.Lemmas2 p-2 p-prime
open import Examples.Groups.Symplectic.BR.Three.Lemmas3 p-2 p-prime hiding (module L02)
open import Examples.Groups.Symplectic.BR.Three.Lemmas4 p-2 p-prime
open import Examples.Groups.Symplectic.BR.Three.Lemmas5 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Embeding-2n p-2 p-prime 1 renaming (f* to emb ; by-emb' to lemma-cong⇣' ; by-emb to lemma-cong⇣ )

open PB (3 QRel,_===_)
open PP (3 QRel,_===_)
-- module B2 = PB (2 QRel,_===_)
-- module P2 = PP (2 QRel,_===_)
-- module B1 = PB (1 QRel,_===_)
-- module P1 = PP (1 QRel,_===_)
open SR word-setoid
open Pattern-Assoc
open Lemmas0 1
module L02 = Lemmas0 2
open Lemmas-2Q 1
--module L2Q0 = Lemmas-2Q 0
open Sym0-Rewriting 2
open Rewriting-Powers 2
open Rewriting-Swap 2
open Rewriting-Swap0 2
open Symplectic-GroupLike
open Basis-Change _ (3 QRel,_===_) grouplike
open import Examples.Groups.Symplectic.Lemmas.XEX-Rewriting p-2 p-prime
open Rewriting-EX 2
open Homo 2 renaming (lemma-f* to lemma-f*-EX)
open Commuting-Symplectic 1
open import Data.List hiding (reverse)
open import Examples.Groups.Symplectic.BR.Two.Lemmas p-2 p-prime hiding (sa)
open import Examples.Groups.Symplectic.BR.Two.D p-2 p-prime hiding (dir-of)
open import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime renaming (dir-of to dir-of-dd)
open import Examples.Groups.Symplectic.BR.Three.BB-CZ p-2 p-prime renaming (dir-of to dir-of-bb)

b'-of-cz : B -> B
b'-of-cz = id

dir-of : B -> Word (Gen 3)
dir-of _ = CZ02

lemma-dir-and-b'-cz : ∀ (b : B) ->
  let
  dir = dir-of b
  b' = b'-of b
  in
  
  [ b ]ᵇ ↑ • CZ ≈ dir • [ b' ]ᵇ ↑

lemma-dir-and-b'-cz b@(ab@(₀ , b) ∷ cd@(₀ , d) ∷ []) = ?
  where
  dir = dir-of b
  b' = b'-of b

