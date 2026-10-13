{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij254 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00884 as MV00884
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00885 as MV00885
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X25 • M4 ≈ M4 • X25
proved = GL.•-cancelʳ {g = X25 • M4} {g' = M4 • X25} {h = p (s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00884.proved (MV00885.proved))) (trans (cong refl Base.proved) (move-product MV00885.proved (MV00884.proved))))
