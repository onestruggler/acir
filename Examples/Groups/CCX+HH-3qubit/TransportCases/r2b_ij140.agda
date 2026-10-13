{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij140 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00806 as MV00806
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00807 as MV00807
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X14 • M0 ≈ M0 • X14
proved = GL.•-cancelʳ {g = X14 • M0} {g' = M0 • X14} {h = p (s3 • s2)}
  (trans (sym (move-product MV00806.proved (MV00807.proved))) (trans (cong refl Base.proved) (move-product MV00807.proved (MV00806.proved))))
