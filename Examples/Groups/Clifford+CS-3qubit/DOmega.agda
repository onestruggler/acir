------------------------------------------------------------------------
-- Presentations of groups
--
-- Bian and Selinger's 3-qubit Clifford+CS circuits, read in U₈(𝔻[ω])
--
-- The relations of Figure 2 are a sub-presentation of U₈(𝔻[i])
-- (Presentation, over the paper's alphabet; Circuits.Presentation, as
-- circuits on three wires), and U₈(𝔻[i]) is a subgroup of U₈(𝔻[ω])
-- (Clifford+CS-TwoLevel.DOmega.Embed), so both are sub-presentations
-- of U₈(𝔻[ω]): two words, or two circuits, are equal by the relations
-- exactly when their matrices over 𝔻[ω] are equal (sound, complete;
-- circuit-sound, circuit-complete).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-3qubit.DOmega where

open import Presentation.Definitions using (_IsSubPresentationOf_)
import Presentation.Embedding as PE

open import Examples.Groups.Clifford+CS-3qubit.Theorem using (module CliffordCS)
open CliffordCS using (Rel)
import Examples.Groups.Clifford+CS-3qubit.Circuits.Syntactics as C
import Examples.Groups.Clifford+CS-3qubit.Presentation as P
import Examples.Groups.Clifford+CS-3qubit.Circuits.Presentation as PC
import Examples.Groups.Clifford+CS-TwoLevel.DOmega as CSΩ
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U)

-- Over the paper's alphabet ...
presentation : Rel IsSubPresentationOf U 8
presentation = CSΩ.Embed.along 8 P.presentation

open PE.Sub presentation public using (⟦_⟧ ; sound ; complete)

-- ... and as circuits.
circuit-presentation : C._VRel,_===_ 3 IsSubPresentationOf U 8
circuit-presentation = CSΩ.Embed.along 8 PC.presentation

open PE.Sub circuit-presentation public
  renaming (⟦_⟧ to circuit⟦_⟧ ; sound to circuit-sound ; complete to circuit-complete)
