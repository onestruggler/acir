{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij120 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00635 as MV00635
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00785 as MV00785
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X12 • M0 ≈ M0 • X12
proved = GL.•-cancelʳ {g = X12 • M0} {g' = M0 • X12} {h = p (ε)}
  (trans (sym (move-product MV00785.proved (MV00635.proved))) (trans (cong refl Base.proved) (move-product MV00635.proved (MV00785.proved))))
