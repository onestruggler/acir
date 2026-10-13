{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij2457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00702 as MV00702
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02948 as MV02948
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02949 as MV02949
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K2457 ≈ M2 • K2457 • M2 • K2457 • M2
proved = GL.•-cancelʳ {g = X45 • K2457} {g' = M2 • K2457 • M2 • K2457 • M2} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02948.proved (MV00702.proved))) (trans (cong refl Base.proved) (move-product MV02949.proved (move-product MV00702.proved (move-product MV02949.proved (move-product MV00702.proved (MV02949.proved)))))))
