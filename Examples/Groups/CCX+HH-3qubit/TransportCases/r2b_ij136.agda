{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij136 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00802 as MV00802
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00803 as MV00803
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X13 • M6 ≈ M6 • X13
proved = GL.•-cancelʳ {g = X13 • M6} {g' = M6 • X13} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2)}
  (trans (sym (move-product MV00802.proved (MV00803.proved))) (trans (cong refl Base.proved) (move-product MV00803.proved (MV00802.proved))))
