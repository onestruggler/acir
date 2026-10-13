{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij04 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00635 as MV00635
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01805 as MV01805
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M0 • M4 ≈ M4 • M0
proved = GL.•-cancelʳ {g = M0 • M4} {g' = M4 • M0} {h = p (ε)}
  (trans (sym (move-product MV00635.proved (MV01805.proved))) (trans (cong refl Base.proved) (move-product MV01805.proved (MV00635.proved))))
