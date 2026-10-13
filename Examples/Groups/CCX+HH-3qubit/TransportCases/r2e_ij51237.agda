{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij51237 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02217 as MV02217
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02218 as MV02218
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M5 • K1237 ≈ K1237 • M5
proved = GL.•-cancelʳ {g = M5 • K1237} {g' = K1237 • M5} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02217.proved (MV02218.proved))) (trans (cong refl Base.proved) (move-product MV02218.proved (MV02217.proved))))
