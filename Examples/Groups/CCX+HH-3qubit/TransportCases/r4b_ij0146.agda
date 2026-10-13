{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0146 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00650 as MV00650
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02846 as MV02846
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02847 as MV02847
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X14 • K0146 ≈ M0 • K0146 • M0 • K0146 • M0
proved = GL.•-cancelʳ {g = X14 • K0146} {g' = M0 • K0146 • M0 • K0146 • M0} {h = p (s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02846.proved (MV00650.proved))) (trans (cong refl Base.proved) (move-product MV02847.proved (move-product MV00650.proved (move-product MV02847.proved (move-product MV00650.proved (MV02847.proved)))))))
