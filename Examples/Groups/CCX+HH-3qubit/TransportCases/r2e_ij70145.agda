{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij70145 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02325 as MV02325
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02326 as MV02326
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M7 • K0145 ≈ K0145 • M7
proved = GL.•-cancelʳ {g = M7 • K0145} {g' = K0145 • M7} {h = p (s3 • s2 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02325.proved (MV02326.proved))) (trans (cong refl Base.proved) (move-product MV02326.proved (MV02325.proved))))
