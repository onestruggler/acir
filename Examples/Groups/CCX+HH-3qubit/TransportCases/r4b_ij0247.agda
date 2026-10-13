{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0247 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00661 as MV00661
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02867 as MV02867
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02868 as MV02868
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • K0247 ≈ M0 • K0247 • M0 • K0247 • M0
proved = GL.•-cancelʳ {g = X24 • K0247} {g' = M0 • K0247 • M0 • K0247 • M0} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02867.proved (MV00661.proved))) (trans (cong refl Base.proved) (move-product MV02868.proved (move-product MV00661.proved (move-product MV02868.proved (move-product MV00661.proved (MV02868.proved)))))))
