{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0157 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00653 as MV00653
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02852 as MV02852
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02853 as MV02853
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X15 • K0157 ≈ M0 • K0157 • M0 • K0157 • M0
proved = GL.•-cancelʳ {g = X15 • K0157} {g' = M0 • K0157 • M0 • K0157 • M0} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02852.proved (MV00653.proved))) (trans (cong refl Base.proved) (move-product MV02853.proved (move-product MV00653.proved (move-product MV02853.proved (move-product MV00653.proved (MV02853.proved)))))))
