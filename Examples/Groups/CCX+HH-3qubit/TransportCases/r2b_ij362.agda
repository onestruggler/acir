{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij362 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00942 as MV00942
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00943 as MV00943
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X36 • M2 ≈ M2 • X36
proved = GL.•-cancelʳ {g = X36 • M2} {g' = M2 • X36} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00942.proved (MV00943.proved))) (trans (cong refl Base.proved) (move-product MV00943.proved (MV00942.proved))))
