{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij132 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00796 as MV00796
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00797 as MV00797
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X13 • M2 ≈ M2 • X13
proved = GL.•-cancelʳ {g = X13 • M2} {g' = M2 • X13} {h = p (s1 • s0 • s1 • s2)}
  (trans (sym (move-product MV00796.proved (MV00797.proved))) (trans (cong refl Base.proved) (move-product MV00797.proved (MV00796.proved))))
