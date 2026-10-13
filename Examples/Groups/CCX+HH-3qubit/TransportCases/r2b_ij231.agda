{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij231 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00856 as MV00856
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00857 as MV00857
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X23 • M1 ≈ M1 • X23
proved = GL.•-cancelʳ {g = X23 • M1} {g' = M1 • X23} {h = p (s0 • s1 • s2)}
  (trans (sym (move-product MV00856.proved (MV00857.proved))) (trans (cong refl Base.proved) (move-product MV00857.proved (MV00856.proved))))
