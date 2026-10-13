{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij172 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00844 as MV00844
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00845 as MV00845
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X17 • M2 ≈ M2 • X17
proved = GL.•-cancelʳ {g = X17 • M2} {g' = M2 • X17} {h = p (s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00844.proved (MV00845.proved))) (trans (cong refl Base.proved) (move-product MV00845.proved (MV00844.proved))))
