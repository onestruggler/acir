{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij61234 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02282 as MV02282
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02283 as MV02283
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M6 • K1234 ≈ K1234 • M6
proved = GL.•-cancelʳ {g = M6 • K1234} {g' = K1234 • M6} {h = p (s0 • s1 • s2 • s3 • s5 • s4)}
  (trans (sym (move-product MV02282.proved (MV02283.proved))) (trans (cong refl Base.proved) (move-product MV02283.proved (MV02282.proved))))
