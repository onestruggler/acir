{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0134 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00645 as MV00645
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01803 as MV01803
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02837 as MV02837
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X13 • K0134 ≈ M0 • K0134 • M0 • K0134 • M0
proved = GL.•-cancelʳ {g = X13 • K0134} {g' = M0 • K0134 • M0 • K0134 • M0} {h = p (s2 • s3)}
  (trans (sym (move-product MV02837.proved (MV00645.proved))) (trans (cong refl Base.proved) (move-product MV01803.proved (move-product MV00645.proved (move-product MV01803.proved (move-product MV00645.proved (MV01803.proved)))))))
