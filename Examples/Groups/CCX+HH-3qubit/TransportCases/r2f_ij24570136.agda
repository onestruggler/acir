{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij24570136 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00702 as MV00702
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02442 as MV02442
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K2457 • K0136 ≈ K0136 • K2457
proved = GL.•-cancelʳ {g = K2457 • K0136} {g' = K0136 • K2457} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00702.proved (MV02442.proved))) (trans (cong refl Base.proved) (move-product MV02442.proved (MV00702.proved))))
