{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij2567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00704 as MV00704
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02807 as MV02807
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02808 as MV02808
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02809 as MV02809
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02810 as MV02810
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X25 • K2567 ≈ K2567 • X57 • M5 • M7
proved = GL.•-cancelʳ {g = X25 • K2567} {g' = K2567 • X57 • M5 • M7} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02807.proved (MV00704.proved))) (trans (cong refl Base.proved) (move-product MV00704.proved (move-product MV02808.proved (move-product MV02809.proved (MV02810.proved))))))
