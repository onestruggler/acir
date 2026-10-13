{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij2457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00702 as MV00702
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02800 as MV02800
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03024 as MV03024
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X57 • K2457 ≈ K2457 • X47
proved = GL.•-cancelʳ {g = X57 • K2457} {g' = K2457 • X47} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03024.proved (MV00702.proved))) (trans (cong refl Base.proved) (move-product MV00702.proved (MV02800.proved))))
