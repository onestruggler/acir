{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij2457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00702 as MV00702
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02799 as MV02799
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02800 as MV02800
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02801 as MV02801
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02802 as MV02802
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • K2457 ≈ K2457 • X47 • M4 • M7
proved = GL.•-cancelʳ {g = X24 • K2457} {g' = K2457 • X47 • M4 • M7} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02799.proved (MV00702.proved))) (trans (cong refl Base.proved) (move-product MV00702.proved (move-product MV02800.proved (move-product MV02801.proved (MV02802.proved))))))
