{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij267 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00900 as MV00900
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00901 as MV00901
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X26 • M7 ≈ M7 • X26
proved = GL.•-cancelʳ {g = X26 • M7} {g' = M7 • X26} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00900.proved (MV00901.proved))) (trans (cong refl Base.proved) (move-product MV00901.proved (MV00900.proved))))
