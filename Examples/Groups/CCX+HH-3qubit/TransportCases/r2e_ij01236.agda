{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij01236 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00677 as MV00677
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01901 as MV01901
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M0 • K1236 ≈ K1236 • M0
proved = GL.•-cancelʳ {g = M0 • K1236} {g' = K1236 • M0} {h = p (s0 • s1 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01901.proved (MV00677.proved))) (trans (cong refl Base.proved) (move-product MV00677.proved (MV01901.proved))))
