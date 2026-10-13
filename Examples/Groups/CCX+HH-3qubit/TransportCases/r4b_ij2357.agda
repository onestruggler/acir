{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij2357 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00699 as MV00699
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02942 as MV02942
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02943 as MV02943
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • K2357 ≈ M2 • K2357 • M2 • K2357 • M2
proved = GL.•-cancelʳ {g = X35 • K2357} {g' = M2 • K2357 • M2 • K2357 • M2} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02942.proved (MV00699.proved))) (trans (cong refl Base.proved) (move-product MV02943.proved (move-product MV00699.proved (move-product MV02943.proved (move-product MV00699.proved (MV02943.proved)))))))
