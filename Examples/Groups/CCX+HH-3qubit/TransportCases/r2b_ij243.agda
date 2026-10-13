{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij243 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00870 as MV00870
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00871 as MV00871
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • M3 ≈ M3 • X24
proved = GL.•-cancelʳ {g = X24 • M3} {g' = M3 • X24} {h = p (s2 • s1 • s0 • s2 • s1 • s3 • s2)}
  (trans (sym (move-product MV00870.proved (MV00871.proved))) (trans (cong refl Base.proved) (move-product MV00871.proved (MV00870.proved))))
