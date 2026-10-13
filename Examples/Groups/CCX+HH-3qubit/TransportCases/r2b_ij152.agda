{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij152 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00820 as MV00820
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00821 as MV00821
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X15 • M2 ≈ M2 • X15
proved = GL.•-cancelʳ {g = X15 • M2} {g' = M2 • X15} {h = p (s1 • s0 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00820.proved (MV00821.proved))) (trans (cong refl Base.proved) (move-product MV00821.proved (MV00820.proved))))
