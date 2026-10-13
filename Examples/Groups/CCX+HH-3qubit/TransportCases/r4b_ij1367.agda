{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1367 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00690 as MV00690
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02924 as MV02924
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02925 as MV02925
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X36 • K1367 ≈ M1 • K1367 • M1 • K1367 • M1
proved = GL.•-cancelʳ {g = X36 • K1367} {g' = M1 • K1367 • M1 • K1367 • M1} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02924.proved (MV00690.proved))) (trans (cong refl Base.proved) (move-product MV02925.proved (move-product MV00690.proved (move-product MV02925.proved (move-product MV00690.proved (MV02925.proved)))))))
