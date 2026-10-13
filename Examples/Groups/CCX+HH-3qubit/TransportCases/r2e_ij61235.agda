{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij61235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02284 as MV02284
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02285 as MV02285
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M6 • K1235 ≈ K1235 • M6
proved = GL.•-cancelʳ {g = M6 • K1235} {g' = K1235 • M6} {h = p (s0 • s1 • s2 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02284.proved (MV02285.proved))) (trans (cong refl Base.proved) (move-product MV02285.proved (MV02284.proved))))
