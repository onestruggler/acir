{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij054 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00755 as MV00755
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00756 as MV00756
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X05 • M4 ≈ M4 • X05
proved = GL.•-cancelʳ {g = X05 • M4} {g' = M4 • X05} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2)}
  (trans (sym (move-product MV00755.proved (MV00756.proved))) (trans (cong refl Base.proved) (move-product MV00756.proved (MV00755.proved))))
