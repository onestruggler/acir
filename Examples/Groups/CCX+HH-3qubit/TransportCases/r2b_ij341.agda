{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij341 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00916 as MV00916
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00917 as MV00917
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X34 • M1 ≈ M1 • X34
proved = GL.•-cancelʳ {g = X34 • M1} {g' = M1 • X34} {h = p (s0 • s2 • s1 • s3 • s2)}
  (trans (sym (move-product MV00916.proved (MV00917.proved))) (trans (cong refl Base.proved) (move-product MV00917.proved (MV00916.proved))))
