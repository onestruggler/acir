{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij4567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00631 as MV00631
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00632 as MV00632
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02962 as MV02962
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • K4567 ≈ M4 • K4567 • M4 • K4567 • M4
proved = GL.•-cancelʳ {g = X56 • K4567} {g' = M4 • K4567 • M4 • K4567 • M4} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02962.proved (MV00632.proved))) (trans (cong refl Base.proved) (move-product MV00631.proved (move-product MV00632.proved (move-product MV00631.proved (move-product MV00632.proved (MV00631.proved)))))))
