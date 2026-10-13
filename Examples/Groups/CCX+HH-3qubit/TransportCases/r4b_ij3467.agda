{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij3467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00707 as MV00707
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02958 as MV02958
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02959 as MV02959
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X46 • K3467 ≈ M3 • K3467 • M3 • K3467 • M3
proved = GL.•-cancelʳ {g = X46 • K3467} {g' = M3 • K3467 • M3 • K3467 • M3} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02958.proved (MV00707.proved))) (trans (cong refl Base.proved) (move-product MV02959.proved (move-product MV00707.proved (move-product MV02959.proved (move-product MV00707.proved (MV02959.proved)))))))
