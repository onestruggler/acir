{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1347 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00687 as MV00687
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02918 as MV02918
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02919 as MV02919
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X34 • K1347 ≈ M1 • K1347 • M1 • K1347 • M1
proved = GL.•-cancelʳ {g = X34 • K1347} {g' = M1 • K1347 • M1 • K1347 • M1} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02918.proved (MV00687.proved))) (trans (cong refl Base.proved) (move-product MV02919.proved (move-product MV00687.proved (move-product MV02919.proved (move-product MV00687.proved (MV02919.proved)))))))
