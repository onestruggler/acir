{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij230 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00854 as MV00854
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00855 as MV00855
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X23 • M0 ≈ M0 • X23
proved = GL.•-cancelʳ {g = X23 • M0} {g' = M0 • X23} {h = p (s1 • s2)}
  (trans (sym (move-product MV00854.proved (MV00855.proved))) (trans (cong refl Base.proved) (move-product MV00855.proved (MV00854.proved))))
