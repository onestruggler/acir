{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij452 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00966 as MV00966
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00967 as MV00967
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • M2 ≈ M2 • X45
proved = GL.•-cancelʳ {g = X45 • M2} {g' = M2 • X45} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00966.proved (MV00967.proved))) (trans (cong refl Base.proved) (move-product MV00967.proved (MV00966.proved))))
