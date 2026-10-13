{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij12470356 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00681 as MV00681
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02421 as MV02421
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K1247 • K0356 ≈ K0356 • K1247
proved = GL.•-cancelʳ {g = K1247 • K0356} {g' = K0356 • K1247} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00681.proved (MV02421.proved))) (trans (cong refl Base.proved) (move-product MV02421.proved (MV00681.proved))))
