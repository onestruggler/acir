{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij045 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00743 as MV00743
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00744 as MV00744
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X04 • M5 ≈ M5 • X04
proved = GL.•-cancelʳ {g = X04 • M5} {g' = M5 • X04} {h = p (s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2)}
  (trans (sym (move-product MV00743.proved (MV00744.proved))) (trans (cong refl Base.proved) (move-product MV00744.proved (MV00743.proved))))
