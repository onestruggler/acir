{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij14 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00000 as MV00000
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00028 as MV00028
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M1 • M4 ≈ M4 • M1
proved = GL.•-cancelʳ {g = M1 • M4} {g' = M4 • M1} {h = p (s0)}
  (trans (sym (move-product MV00000.proved (MV00028.proved))) (trans (cong refl Base.proved) (move-product MV00028.proved (MV00000.proved))))
