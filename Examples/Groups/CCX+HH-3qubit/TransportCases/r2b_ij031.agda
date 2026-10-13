{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij031 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00725 as MV00725
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00726 as MV00726
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X03 • M1 ≈ M1 • X03
proved = GL.•-cancelʳ {g = X03 • M1} {g' = M1 • X03} {h = p (s0 • s2)}
  (trans (sym (move-product MV00725.proved (MV00726.proved))) (trans (cong refl Base.proved) (move-product MV00726.proved (MV00725.proved))))
