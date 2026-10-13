{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0137 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00648 as MV00648
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02583 as MV02583
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02584 as MV02584
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02585 as MV02585
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02586 as MV02586
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X01 • K0137 ≈ K0137 • X17 • M1 • M7
proved = GL.•-cancelʳ {g = X01 • K0137} {g' = K0137 • X17 • M1 • M7} {h = p (s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02583.proved (MV00648.proved))) (trans (cong refl Base.proved) (move-product MV00648.proved (move-product MV02584.proved (move-product MV02585.proved (MV02586.proved))))))
