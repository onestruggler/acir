{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij016 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00639 as MV00639
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00713 as MV00713
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X01 • M6 ≈ M6 • X01
proved = GL.•-cancelʳ {g = X01 • M6} {g' = M6 • X01} {h = p (s5 • s4 • s3 • s2 • s1 • s0)}
  (trans (sym (move-product MV00713.proved (MV00639.proved))) (trans (cong refl Base.proved) (move-product MV00639.proved (MV00713.proved))))
