{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij342 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00918 as MV00918
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00919 as MV00919
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X34 • M2 ≈ M2 • X34
proved = GL.•-cancelʳ {g = X34 • M2} {g' = M2 • X34} {h = p (s1 • s0 • s2 • s1 • s3 • s2)}
  (trans (sym (move-product MV00918.proved (MV00919.proved))) (trans (cong refl Base.proved) (move-product MV00919.proved (MV00918.proved))))
