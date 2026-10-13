{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0124 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00003 as MV00003
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00106 as MV00106
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as MV00245
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X12 • K0124 ≈ M0 • K0124 • M0 • K0124 • M0
proved = GL.•-cancelʳ {g = X12 • K0124} {g' = M0 • K0124 • M0 • K0124 • M0} {h = p (s3)}
  (trans (sym (move-product MV00106.proved (MV00245.proved))) (trans (cong refl Base.proved) (move-product MV00003.proved (move-product MV00245.proved (move-product MV00003.proved (move-product MV00245.proved (MV00003.proved)))))))
