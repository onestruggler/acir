------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding's gadgets in the spellings of the four-wire derivations
--
-- The decoding (Decoding, MultiControlled) builds its gadgets from the
-- S-box and the K-box placed by swap networks; the four-wire
-- derivations (Four.D) state their facts about the macro spellings of
-- scratchpad/gadgets4.py.  The bridge is a re-bracketing of the closed
-- word followed by swap pushes (`lem-bridge-G-pp`, generated): the
-- phase gadget at four wires is Toff₀₁₂ CS₀₃ Toff₀₁₂ CS₀₃⁻¹.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Proofs ; Win ; get)
open import Examples.Groups.Clifford+CS.Four.CStmt using (clemmas)

module Examples.Groups.Clifford+CS.Four.Bridge (C : Proofs clemmas) where

open import Data.List using (List ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (G-pp)
open import Examples.Groups.Clifford+CS.Four.Chain

-- The lemmas of Four/D it uses (Four.CStmt; Four.ConsInst gives them).
private
  lem-bridge-G-pp : Win clemmas 477
  lem-bridge-G-pp = get clemmas C 477

-- The phase gadget L₁₂₃(iZ₀) of the decoding, as the derivations spell it.
G-pp-≈ : G-pp 1 ≈ ⟪ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [] ⟫ʷ
G-pp-≈ = trans (by-assoc Eq.refl) lem-bridge-G-pp
