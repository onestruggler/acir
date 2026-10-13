{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij2346 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00696 as MV00696
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02936 as MV02936
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02937 as MV02937
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X34 • K2346 ≈ M2 • K2346 • M2 • K2346 • M2
proved = GL.•-cancelʳ {g = X34 • K2346} {g' = M2 • K2346 • M2 • K2346 • M2} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02936.proved (MV00696.proved))) (trans (cong refl Base.proved) (move-product MV02937.proved (move-product MV00696.proved (move-product MV02937.proved (move-product MV00696.proved (MV02937.proved)))))))
