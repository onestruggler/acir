{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij064 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00767 as MV00767
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00768 as MV00768
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X06 • M4 ≈ M4 • X06
proved = GL.•-cancelʳ {g = X06 • M4} {g' = M4 • X06} {h = p (s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00767.proved (MV00768.proved))) (trans (cong refl Base.proved) (move-product MV00768.proved (MV00767.proved))))
