{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij163 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00834 as MV00834
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00835 as MV00835
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X16 • M3 ≈ M3 • X16
proved = GL.•-cancelʳ {g = X16 • M3} {g' = M3 • X16} {h = p (s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00834.proved (MV00835.proved))) (trans (cong refl Base.proved) (move-product MV00835.proved (MV00834.proved))))
