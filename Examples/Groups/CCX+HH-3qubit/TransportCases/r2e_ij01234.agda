{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij01234 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00675 as MV00675
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01811 as MV01811
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M0 • K1234 ≈ K1234 • M0
proved = GL.•-cancelʳ {g = M0 • K1234} {g' = K1234 • M0} {h = p (s0 • s1 • s2 • s3)}
  (trans (sym (move-product MV01811.proved (MV00675.proved))) (trans (cong refl Base.proved) (move-product MV00675.proved (MV01811.proved))))
