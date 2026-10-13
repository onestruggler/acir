{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij71235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02353 as MV02353
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02354 as MV02354
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M7 • K1235 ≈ K1235 • M7
proved = GL.•-cancelʳ {g = M7 • K1235} {g' = K1235 • M7} {h = p (s0 • s1 • s2 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02353.proved (MV02354.proved))) (trans (cong refl Base.proved) (move-product MV02354.proved (MV02353.proved))))
