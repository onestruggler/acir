{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0146 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00650 as MV00650
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02591 as MV02591
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02592 as MV02592
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02593 as MV02593
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02594 as MV02594
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X01 • K0146 ≈ K0146 • X16 • M1 • M6
proved = GL.•-cancelʳ {g = X01 • K0146} {g' = K0146 • X16 • M1 • M6} {h = p (s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02591.proved (MV00650.proved))) (trans (cong refl Base.proved) (move-product MV00650.proved (move-product MV02592.proved (move-product MV02593.proved (MV02594.proved))))))
