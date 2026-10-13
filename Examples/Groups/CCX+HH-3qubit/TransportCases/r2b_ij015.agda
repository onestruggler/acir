{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij015 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00638 as MV00638
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00712 as MV00712
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X01 • M5 ≈ M5 • X01
proved = GL.•-cancelʳ {g = X01 • M5} {g' = M5 • X01} {h = p (s4 • s3 • s2 • s1 • s0)}
  (trans (sym (move-product MV00712.proved (MV00638.proved))) (trans (cong refl Base.proved) (move-product MV00638.proved (MV00712.proved))))
