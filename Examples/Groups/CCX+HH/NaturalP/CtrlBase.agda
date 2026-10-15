------------------------------------------------------------------------
-- Presentations of groups
--
-- The controlled gadgets of NaturalP.Ctrl on their own wires.
--
-- Each gadget acts as its gate controlled by wire 0 at the smallest
-- width it is defined at, decided on the basis columns
-- (NaturalP.Columns): XC, the Toffoli CCXc and the Fredkin gate on two
-- and three wires, CHHa and CHHb (controlled HH, a wire borrowed) on
-- four.  The controlled Toffolis C3Xa and C3Xb, on five wires, are in
-- NaturalP.CtrlBase5.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.CtrlBase where

open import Data.Nat.Base using (zero ; suc ; _^_)
open import Notations using (₂₊ ; ₃₊)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Examples.Groups.CCX+HH.Natural.Syntactics as N
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ)
open import Examples.Groups.CCX+HH.NaturalP.Ctrl
open import Examples.Groups.CCX+HH.NaturalP.Columns using (ctrl-by-columns)
open import Examples.Groups.CCX+HH.NaturalP.Blocks2 using (ctrlA)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (quantum)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
import Examples.Groups.Clifford+CS-TwoLevel.Vector as V

import Examples.Groups.CCX+HH.StructuralEncoding as E
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (isCommutativeRing-D ; adj-D ; ½ᴰ)
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (encode-parallel)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating)
open import Examples.Groups.CCX+HH.NaturalP.Columns using (agree)
open import Data.Bool.Base using (T)
open import Word.Base using (ε)

-- Each check is named with its full type: inlined as the argument of
-- ctrl-by-columns, `tt` exhausted memory (the boolean itself takes a
-- second).
private
  opaque
    unfolding A.actV V.set₁ V.set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

    XC-chk : T (agree (E.encode (N.XC {zero}))
                 (encode-parallel (alternating (2 ^ suc zero)) ε (E.encode (N.X {zero}))))
    XC-chk = tt

    CCXc-chk : T (agree (E.encode (τ (CCXc {zero})))
                 (encode-parallel (alternating (2 ^ ₂₊ zero)) ε (E.encode (N.CX {zero}))))
    CCXc-chk = tt

    Fredkin-chk : T (agree (E.encode (τ (Fredkin {zero})))
                 (encode-parallel (alternating (2 ^ ₂₊ zero)) ε (E.encode (N.Ex {zero}))))
    Fredkin-chk = tt

    CHHa-chk : T (agree (E.encode (τ (CHHa {zero})))
                 (encode-parallel (alternating (2 ^ ₃₊ zero)) ε (E.encode (N.HH {suc zero}))))
    CHHa-chk = tt

    CHHb-chk : T (agree (E.encode (τ (CHHb {zero})))
                 (encode-parallel (alternating (2 ^ ₃₊ zero)) ε (E.encode (N.HH {zero} N.↑))))
    CHHb-chk = tt

XC-base : ∀ x → quantum (N.XC {zero}) x ≡ ctrlA (2 ^ suc zero) (quantum (N.X {zero})) x
XC-base = ctrl-by-columns (N.XC {zero}) (N.X {zero}) XC-chk

CCXc-base : ∀ x → quantum (τ (CCXc {zero})) x ≡ ctrlA (2 ^ ₂₊ zero) (quantum (N.CX {zero})) x
CCXc-base = ctrl-by-columns (τ (CCXc {zero})) (N.CX {zero}) CCXc-chk

Fredkin-base : ∀ x → quantum (τ (Fredkin {zero})) x ≡ ctrlA (2 ^ ₂₊ zero) (quantum (N.Ex {zero})) x
Fredkin-base = ctrl-by-columns (τ (Fredkin {zero})) (N.Ex {zero}) Fredkin-chk

CHHa-base : ∀ x → quantum (τ (CHHa {zero})) x ≡ ctrlA (2 ^ ₃₊ zero) (quantum (N.HH {suc zero})) x
CHHa-base = ctrl-by-columns (τ (CHHa {zero})) (N.HH {suc zero}) CHHa-chk

CHHb-base : ∀ x → quantum (τ (CHHb {zero})) x ≡ ctrlA (2 ^ ₃₊ zero) (quantum (N.HH {zero} N.↑)) x
CHHb-base = ctrl-by-columns (τ (CHHb {zero})) (N.HH {zero} N.↑) CHHb-chk

