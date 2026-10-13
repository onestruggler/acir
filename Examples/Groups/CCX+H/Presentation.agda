------------------------------------------------------------------------
-- Presentations of groups
--
-- An unconditional complete equational theory for X,CX,CCX,H at every
-- width, with independent 2^n by 2^n physical tensor matrices.
-- Each fixed-width rule set is Clément's decoded-source translation
-- together with gate recovery equations.  No ancillary wires occur.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.Presentation where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (WRel)
import Presentation.Base as PB
open import Examples.Groups.CCX+H.Syntactics using (Gen ; Circuit)
open import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics public
  using (gate-matrix ; interpret)
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as Sem
import Examples.Groups.CCX+H.GeneralN.SmallPhysicalSemantics as Small
import Examples.Groups.CCX+H.Zero as Zero
import Examples.Groups.CCX+H.OneQubit as One
import Examples.Groups.CCX+H.TwoQubit as Two
import Examples.Groups.CCX+H.ThreeQubit.Presentation as Three
import Examples.Groups.CCX+H.GeneralN.CircuitPresentation as General

Relations : (n : ℕ) → WRel (Gen n)
Relations 0 = Zero.Empty
Relations 1 = One._===_
Relations 2 = Two._===_
Relations 3 = Three._===_
Relations (suc (suc (suc (suc n)))) = General._===_ n

infix 4 _⊢_≈_
_⊢_≈_ : (n : ℕ) → Circuit n → Circuit n → Set
n ⊢ u ≈ v = PB._≈_ (Relations n) u v

sound : ∀ n {u v} → n ⊢ u ≈ v → interpret u ≡ interpret v
sound 0 {u} {v} eq = Eq.trans (Small.zero-identity u) (Eq.sym (Small.zero-identity v))
sound 1 {u} {v} eq = Eq.trans (Small.one u)
  (Eq.trans (One.sound {w = u} {v = v} eq) (Eq.sym (Small.one v)))
sound 2 {u} {v} eq = Eq.trans (Small.two u)
  (Eq.trans (Two.sound {w = u} {v = v} eq) (Eq.sym (Small.two v)))
sound 3 {u} {v} eq = Eq.trans (Small.three u)
  (Eq.trans (Three.sound {w = u} {v = v} eq) (Eq.sym (Small.three v)))
sound (suc (suc (suc (suc n)))) {u} {v} eq =
  Sem.At.forward (3 + n) {u} {v} (General.sound n {u} {v} eq)

complete : ∀ n {u v} → interpret u ≡ interpret v → n ⊢ u ≈ v
complete 0 {u} {v} eq = Zero.complete u v
complete 1 {u} {v} eq = One.complete (Eq.trans (Eq.sym (Small.one u)) (Eq.trans eq (Small.one v)))
complete 2 {u} {v} eq = Two.complete (Eq.trans (Eq.sym (Small.two u)) (Eq.trans eq (Small.two v)))
complete 3 {u} {v} eq = Three.complete (Eq.trans (Eq.sym (Small.three u)) (Eq.trans eq (Small.three v)))
complete (suc (suc (suc (suc n)))) {u} {v} eq =
  General.complete n {u} {v} (Sem.At.backward (3 + n) {u} {v} eq)
