{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij3 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00630 as MV00630
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R083 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M3 • M3 ≈ ε
proved = GL.•-cancelʳ {g = M3 • M3} {g' = ε} {h = p (s2 • s1 • s0)}
  (trans (sym (move-product MV00630.proved (MV00630.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
