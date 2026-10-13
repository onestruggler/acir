{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij51234 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02213 as MV02213
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02214 as MV02214
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M5 • K1234 ≈ K1234 • M5
proved = GL.•-cancelʳ {g = M5 • K1234} {g' = K1234 • M5} {h = p (s0 • s1 • s2 • s3 • s4)}
  (trans (sym (move-product MV02213.proved (MV02214.proved))) (trans (cong refl Base.proved) (move-product MV02214.proved (MV02213.proved))))
