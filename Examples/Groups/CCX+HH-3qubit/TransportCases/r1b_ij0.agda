{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij0 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00635 as MV00635
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R083 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M0 • M0 ≈ ε
proved = GL.•-cancelʳ {g = M0 • M0} {g' = ε} {h = p (ε)}
  (trans (sym (move-product MV00635.proved (MV00635.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
