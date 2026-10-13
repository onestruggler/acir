{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0245 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00659 as MV00659
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02863 as MV02863
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02864 as MV02864
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • K0245 ≈ M0 • K0245 • M0 • K0245 • M0
proved = GL.•-cancelʳ {g = X24 • K0245} {g' = M0 • K0245 • M0 • K0245 • M0} {h = p (s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02863.proved (MV00659.proved))) (trans (cong refl Base.proved) (move-product MV02864.proved (move-product MV00659.proved (move-product MV02864.proved (move-product MV00659.proved (MV02864.proved)))))))
