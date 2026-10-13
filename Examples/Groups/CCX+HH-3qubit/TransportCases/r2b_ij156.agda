{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij156 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00826 as MV00826
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00827 as MV00827
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X15 • M6 ≈ M6 • X15
proved = GL.•-cancelʳ {g = X15 • M6} {g' = M6 • X15} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00826.proved (MV00827.proved))) (trans (cong refl Base.proved) (move-product MV00827.proved (MV00826.proved))))
