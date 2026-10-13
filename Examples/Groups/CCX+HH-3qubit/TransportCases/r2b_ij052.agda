{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij052 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00751 as MV00751
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00752 as MV00752
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X05 • M2 ≈ M2 • X05
proved = GL.•-cancelʳ {g = X05 • M2} {g' = M2 • X05} {h = p (s1 • s0 • s4 • s3 • s2)}
  (trans (sym (move-product MV00751.proved (MV00752.proved))) (trans (cong refl Base.proved) (move-product MV00752.proved (MV00751.proved))))
