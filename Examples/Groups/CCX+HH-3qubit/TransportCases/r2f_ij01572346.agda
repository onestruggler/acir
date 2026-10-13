{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01572346 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00653 as MV00653
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02393 as MV02393
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0157 • K2346 ≈ K2346 • K0157
proved = GL.•-cancelʳ {g = K0157 • K2346} {g' = K2346 • K0157} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00653.proved (MV02393.proved))) (trans (cong refl Base.proved) (move-product MV02393.proved (MV00653.proved))))
