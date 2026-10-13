{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij071 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00773 as MV00773
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00774 as MV00774
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X07 • M1 ≈ M1 • X07
proved = GL.•-cancelʳ {g = X07 • M1} {g' = M1 • X07} {h = p (s0 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00773.proved (MV00774.proved))) (trans (cong refl Base.proved) (move-product MV00774.proved (MV00773.proved))))
