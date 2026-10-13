{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0357 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00669 as MV00669
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02883 as MV02883
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02884 as MV02884
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • K0357 ≈ M0 • K0357 • M0 • K0357 • M0
proved = GL.•-cancelʳ {g = X35 • K0357} {g' = M0 • K0357 • M0 • K0357 • M0} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02883.proved (MV00669.proved))) (trans (cong refl Base.proved) (move-product MV02884.proved (move-product MV00669.proved (move-product MV02884.proved (move-product MV00669.proved (MV02884.proved)))))))
