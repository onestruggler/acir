{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij123 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00786 as MV00786
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00787 as MV00787
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X12 • M3 ≈ M3 • X12
proved = GL.•-cancelʳ {g = X12 • M3} {g' = M3 • X12} {h = p (s2 • s1 • s0 • s1 • s2)}
  (trans (sym (move-product MV00786.proved (MV00787.proved))) (trans (cong refl Base.proved) (move-product MV00787.proved (MV00786.proved))))
