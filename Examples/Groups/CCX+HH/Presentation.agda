------------------------------------------------------------------------
-- Presentations of groups
--
-- Complete circuit relations for X, CX, CCX and HH at every width.
-- The small finite cases and the four-state Clément translation share
-- the same independent ordinary matrix semantics.  No theorem parameter
-- or semantic-equality axiom remains in this interface.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Presentation where

open import Data.Nat.Base using (ℕ ; suc)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Word.Base using (WRel ; [_]ʷ)
open import Presentation.GroupLike using (Grouplike)
import Presentation.Base as PB
open import Examples.Groups.CCX+HH.Syntactics using (Gen ; Circuit)
import Examples.Groups.CCX+HH.Semantics as C
import Examples.Groups.CCX+HH.LowWidth as Low
import Examples.Groups.CCX+HH.ThreeQubit.Presentation as Three
import Examples.Groups.CCX+HH.GeneralN.Presentation as General
open import Examples.Groups.CCX+HH.GeneralN.GateInvolutions
  using (matrix-involutive)

infix 4 _===_ _≈_

_===_ : ∀ {n} → WRel (Gen n)
_===_ {0} = Low.Zero._===_
_===_ {1} = Low.One._===_
_===_ {2} = Low.Two._===_
_===_ {3} = Three._===_
_===_ {suc (suc (suc (suc n)))} = General._===_ n

_≈_ : ∀ {n} → WRel (Gen n)
_≈_ {n} = PB._≈_ (_===_ {n})

soundness : ∀ {n} {u v : Circuit n} → u ≈ v → C.interpret u ≡ C.interpret v
soundness {0} = Low.Zero.soundness
soundness {1} = Low.One.soundness
soundness {2} = Low.Two.soundness
soundness {3} = Three.soundness
soundness {suc (suc (suc (suc n)))} = General.sound n

completeness : ∀ {n} {u v : Circuit n} → C.interpret u ≡ C.interpret v → u ≈ v
completeness {0} = Low.Zero.completeness
completeness {1} = Low.One.completeness
completeness {2} = Low.Two.completeness
completeness {3} = Three.completeness
completeness {suc (suc (suc (suc n)))} = General.complete n

grouplike : ∀ n → Grouplike (_===_ {n})
grouplike n g = [ g ]ʷ , completeness (matrix-involutive g)
