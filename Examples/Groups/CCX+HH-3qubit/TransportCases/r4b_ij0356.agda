{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0356 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00668 as MV00668
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02881 as MV02881
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02882 as MV02882
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • K0356 ≈ M0 • K0356 • M0 • K0356 • M0
proved = GL.•-cancelʳ {g = X35 • K0356} {g' = M0 • K0356 • M0 • K0356 • M0} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02881.proved (MV00668.proved))) (trans (cong refl Base.proved) (move-product MV02882.proved (move-product MV00668.proved (move-product MV02882.proved (move-product MV00668.proved (MV02882.proved)))))))
