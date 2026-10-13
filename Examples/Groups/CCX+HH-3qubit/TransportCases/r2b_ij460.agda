{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij460 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00974 as MV00974
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00975 as MV00975
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X46 • M0 ≈ M0 • X46
proved = GL.•-cancelʳ {g = X46 • M0} {g' = M0 • X46} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00974.proved (MV00975.proved))) (trans (cong refl Base.proved) (move-product MV00975.proved (MV00974.proved))))
