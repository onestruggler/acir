{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00671 as MV00671
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02887 as MV02887
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02888 as MV02888
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K0456 ≈ M0 • K0456 • M0 • K0456 • M0
proved = GL.•-cancelʳ {g = X45 • K0456} {g' = M0 • K0456 • M0 • K0456 • M0} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02887.proved (MV00671.proved))) (trans (cong refl Base.proved) (move-product MV02888.proved (move-product MV00671.proved (move-product MV02888.proved (move-product MV00671.proved (MV02888.proved)))))))
