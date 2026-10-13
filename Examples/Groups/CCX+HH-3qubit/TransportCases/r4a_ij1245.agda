{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1245 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00679 as MV00679
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02707 as MV02707
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02708 as MV02708
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02709 as MV02709
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02710 as MV02710
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X12 • K1245 ≈ K1245 • X25 • M2 • M5
proved = GL.•-cancelʳ {g = X12 • K1245} {g' = K1245 • X25 • M2 • M5} {h = p (s0 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02707.proved (MV00679.proved))) (trans (cong refl Base.proved) (move-product MV00679.proved (move-product MV02708.proved (move-product MV02709.proved (MV02710.proved))))))
