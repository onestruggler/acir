{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij4 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00637 as MV00637
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R083 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M4 • M4 ≈ ε
proved = GL.•-cancelʳ {g = M4 • M4} {g' = ε} {h = p (s3 • s2 • s1 • s0)}
  (trans (sym (move-product MV00637.proved (MV00637.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
