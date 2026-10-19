------------------------------------------------------------------------
-- Presentations of groups
--
-- The CCX+H rules, with CCXH⁴, are complete on three wires.
--
-- Clément's translation (CCX+HH/Translation) with the decoder of this
-- directory: a circuit relation is the decoding of a relation of
-- Tables 1 and 2 on eight levels, or a generator against the decoding
-- of its encoding, and with these relations the circuits are complete,
-- by the completeness of the scaled two-level presentation.  Every one
-- of those relations is derived from the rules (Relations, Recovery),
-- so the rules are complete.  The derivations are contractions in the
-- graph of the lattices g E8 (CCX+H/Rules3): their squares are the rule
-- CCXH⁴, their backtracks the Clifford group.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.ThreeWire.Complete where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Presentation.Base as PB

open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Kit
  using (_⊢_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)
open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Decoder using (d′)
open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Relations using (decoded)
open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Recovery using (recover)
open import Examples.Groups.CCX+H.NaturalP.Complete using (Complete)
open import Examples.Groups.CCX+H.NaturalP.Soundness using (τH)
import Examples.Groups.CCX+H.NaturalP.Bridge as Br
import Examples.Groups.CCX+H.Syntactics as C
open import Examples.Groups.CCX+H.Encoding using (e ; encode)
open import Examples.Groups.CCX+H.ThreeQubit.Semantics using (bridge) renaming (interpret to interpret₃)
import Examples.Groups.CCX+H.GeneralN.SmallPhysicalSemantics as Small
import Examples.Groups.CCX+HH.Translation as Translation
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Completeness as SC

private
  module Rules = Translation (T._===ᴸ_ {8}) e d′
  module SC3 = SC 3

  ι-ax : ∀ {w v} → w Rules.=== v → 3 ⊢ Br.ι w ≈ Br.ι v
  ι-ax (Rules.decoded h) = decoded h
  ι-ax (Rules.recover x) = recover x

  ι-cong : ∀ {w v} → w Rules.Circuit.≈ v → 3 ⊢ Br.ι w ≈ Br.ι v
  ι-cong PB.refl        = refl
  ι-cong (PB.sym p)     = sym (ι-cong p)
  ι-cong (PB.trans p q) = trans (ι-cong p) (ι-cong q)
  ι-cong (PB.cong p q)  = cong (ι-cong p) (ι-cong q)
  ι-cong PB.assoc       = assoc
  ι-cong PB.left-unit   = left-unit
  ι-cong PB.right-unit  = right-unit
  ι-cong (PB.axiom a)   = ι-ax a

  complete-C : ∀ {w v : C.Circuit 3} → interpret₃ w ≡ interpret₃ v → w Rules.Circuit.≈ v
  complete-C {w} {v} p = Rules.encode-injective
    (SC3.completeness {u = encode w} {v = encode v} (Eq.trans (bridge w) (Eq.trans p (Eq.sym (bridge v)))))

complete₃ : Complete 3
complete₃ {u} {v} p =
  trans (Br.back u)
  (trans (ι-cong (complete-C (Eq.trans (Eq.sym (Small.three (τH u))) (Eq.trans p (Small.three (τH v))))))
         (sym (Br.back v)))
