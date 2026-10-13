{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij134 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00798 as MV00798
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00799 as MV00799
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X13 • M4 ≈ M4 • X13
proved = GL.•-cancelʳ {g = X13 • M4} {g' = M4 • X13} {h = p (s3 • s2 • s1 • s0 • s1 • s3 • s2)}
  (trans (sym (move-product MV00798.proved (MV00799.proved))) (trans (cong refl Base.proved) (move-product MV00799.proved (MV00798.proved))))
