{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij12360457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00677 as MV00677
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02417 as MV02417
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K1236 • K0457 ≈ K0457 • K1236
proved = GL.•-cancelʳ {g = K1236 • K0457} {g' = K0457 • K1236} {h = p (s0 • s1 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00677.proved (MV02417.proved))) (trans (cong refl Base.proved) (move-product MV02417.proved (MV00677.proved))))
