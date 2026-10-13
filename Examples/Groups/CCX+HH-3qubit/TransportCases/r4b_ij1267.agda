{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1267 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00684 as MV00684
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02912 as MV02912
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02913 as MV02913
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X26 • K1267 ≈ M1 • K1267 • M1 • K1267 • M1
proved = GL.•-cancelʳ {g = X26 • K1267} {g' = M1 • K1267 • M1 • K1267 • M1} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02912.proved (MV00684.proved))) (trans (cong refl Base.proved) (move-product MV02913.proved (move-product MV00684.proved (move-product MV02913.proved (move-product MV00684.proved (MV02913.proved)))))))
