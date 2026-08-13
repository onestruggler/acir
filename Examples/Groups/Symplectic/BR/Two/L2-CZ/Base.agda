------------------------------------------------------------------------
-- Presentations of groups
--
-- L2-CZ, the shared context.
--
-- The preamble of L2-CZ costs about 9 CPU seconds on its own -- it
-- instantiates Rewriting-Swap and several Lemmas0 / Lemmas-2Q modules --
-- so the two components import it from here rather than repeating it,
-- and it is elaborated once.  Everything it opens is re-exported.
--
-- intp lives here too: both components mention it, the L' 2 one at
-- inj1 and the L' 1 one at inj2.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe --call-by-name --termination-depth=4 #-}


open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _≟_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec
open import Data.Fin hiding (_+_ ; _-_ ; _≤_ ; _<_)

open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Empty using (⊥-elim)

open import Word.Base hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Notations



open import Presentation.GroupLike
open import Data.Nat.Primality




module Examples.Groups.Symplectic.BR.Two.L2-CZ.Base (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where


n : ℕ
n = 0
    




open import ForStdlib.Data.Fin.Mod public
open import ForStdlib.Data.Fin.Mod.Prime.Properties p-2 p-prime public
open PrimeModulus p-2 p-prime public
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime public
open Symplectic public
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime hiding (M) public

open import Algebra.Properties.Ring (+-*-ring p-2) public


open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime public
--open Lemmas-2Q 2

open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime public
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime public
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3 p-2 p-prime public
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym4 p-2 p-prime public
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2n p-2 p-prime public
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n p-2 p-prime public

open import Examples.Groups.Symplectic.Lemmas.Lemma-Comm p-2 p-prime 0 public
open Lemmas0a1 public
open Lemmas0b hiding (lemma-semi-HH↑-CZ^k'-ℕ ; lemma-semi-HH↑-CZ^k' ; lemma-eqn17↓ ; lemma-comm-Ex-H' ; lemma-XCS^k-ℕ ; lemma-XCS^k' ; lemma-XCS^k ; lemma-HCZHS^k ; lemma-HCZHS) public
open Lemmas0c public
open Lemmas-Sym public


open import Examples.Groups.Symplectic.Lemmas.Lemmas4-Sym p-2 p-prime public
open import Examples.Groups.Symplectic.Normalization.Pushing.DH p-2 p-prime public
open import Examples.Groups.Symplectic.BR.One.A p-2 p-prime public
open import Examples.Groups.Symplectic.BR.Two.Lemmas p-2 p-prime hiding (n ; module L01 ; sa) public
open import Examples.Groups.Symplectic.BR.Two.Lemmas2 p-2 p-prime hiding (n ; module L01) public
open import Examples.Groups.Symplectic.BR.Two.Lemmas3 p-2 p-prime hiding (n ; module L01 ; sa) public
open import Examples.Groups.Symplectic.BR.Two.A-CZ p-2 p-prime hiding (n ; module L01) public


open PB ((₂₊ n) QRel,_===_) public
open PP ((₂₊ n) QRel,_===_) public
open SR word-setoid public
open Pattern-Assoc public
open Lemmas0 n public
module L01 = Lemmas0 1
open Lemmas-2Q n public
open Sym0-Rewriting (₁₊ n) public
open Rewriting-Swap 1 hiding (multistep-trace ; multistep ; lemma-multistep) public
open Symplectic-GroupLike public
open Basis-Change _ (2 QRel,_===_) grouplike public
open Group-Lemmas (2 QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹ʷ) public
open Commuting-Symplectic 0 public



intp : L' 2 ⊎ L' 1 → Word (Gen 2)
intp (inj₁ l) = [ l ]ˡ'
-- the ε mirrors [_]ˡ on the j=1 (empty-vector) L 2 value, so that
-- intp (l'-of l) is definitionally the old [ l'-of l ]ˡ.
intp (inj₂ (_ , a)) = (ε • [ a ]ᵃ) ↑


