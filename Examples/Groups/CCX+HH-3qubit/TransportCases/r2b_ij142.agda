{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij142 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00808 as MV00808
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00809 as MV00809
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X14 • M2 ≈ M2 • X14
proved = GL.•-cancelʳ {g = X14 • M2} {g' = M2 • X14} {h = p (s1 • s0 • s1 • s3 • s2)}
  (trans (sym (move-product MV00808.proved (MV00809.proved))) (trans (cong refl Base.proved) (move-product MV00809.proved (MV00808.proved))))
