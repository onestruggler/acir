{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1367 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00690 as MV00690
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02751 as MV02751
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02752 as MV02752
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02753 as MV02753
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02754 as MV02754
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X13 • K1367 ≈ K1367 • X37 • M3 • M7
proved = GL.•-cancelʳ {g = X13 • K1367} {g' = K1367 • X37 • M3 • M7} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02751.proved (MV00690.proved))) (trans (cong refl Base.proved) (move-product MV00690.proved (move-product MV02752.proved (move-product MV02753.proved (MV02754.proved))))))
