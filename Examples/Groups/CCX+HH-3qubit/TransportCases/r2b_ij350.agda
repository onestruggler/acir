{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij350 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00926 as MV00926
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00927 as MV00927
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • M0 ≈ M0 • X35
proved = GL.•-cancelʳ {g = X35 • M0} {g' = M0 • X35} {h = p (s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00926.proved (MV00927.proved))) (trans (cong refl Base.proved) (move-product MV00927.proved (MV00926.proved))))
