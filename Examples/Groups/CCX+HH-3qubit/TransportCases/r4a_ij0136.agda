{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0136 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00647 as MV00647
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02579 as MV02579
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02580 as MV02580
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02581 as MV02581
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02582 as MV02582
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X01 • K0136 ≈ K0136 • X16 • M1 • M6
proved = GL.•-cancelʳ {g = X01 • K0136} {g' = K0136 • X16 • M1 • M6} {h = p (s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02579.proved (MV00647.proved))) (trans (cong refl Base.proved) (move-product MV00647.proved (move-product MV02580.proved (move-product MV02581.proved (MV02582.proved))))))
