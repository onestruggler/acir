{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij03571246 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00669 as MV00669
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02409 as MV02409
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0357 • K1246 ≈ K1246 • K0357
proved = GL.•-cancelʳ {g = K0357 • K1246} {g' = K1246 • K0357} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00669.proved (MV02409.proved))) (trans (cong refl Base.proved) (move-product MV02409.proved (MV00669.proved))))
