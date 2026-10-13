{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij12450367 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00679 as MV00679
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02419 as MV02419
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K1245 • K0367 ≈ K0367 • K1245
proved = GL.•-cancelʳ {g = K1245 • K0367} {g' = K0367 • K1245} {h = p (s0 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV00679.proved (MV02419.proved))) (trans (cong refl Base.proved) (move-product MV02419.proved (MV00679.proved))))
