{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0135 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00646 as MV00646
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02838 as MV02838
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02839 as MV02839
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X13 • K0135 ≈ M0 • K0135 • M0 • K0135 • M0
proved = GL.•-cancelʳ {g = X13 • K0135} {g' = M0 • K0135 • M0 • K0135 • M0} {h = p (s2 • s4 • s3)}
  (trans (sym (move-product MV02838.proved (MV00646.proved))) (trans (cong refl Base.proved) (move-product MV02839.proved (move-product MV00646.proved (move-product MV02839.proved (move-product MV00646.proved (MV02839.proved)))))))
