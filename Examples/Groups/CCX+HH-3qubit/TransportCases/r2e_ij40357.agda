{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40357 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02139 as MV02139
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02140 as MV02140
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M4 • K0357 ≈ K0357 • M4
proved = GL.•-cancelʳ {g = M4 • K0357} {g' = K0357 • M4} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02139.proved (MV02140.proved))) (trans (cong refl Base.proved) (move-product MV02140.proved (MV02139.proved))))
