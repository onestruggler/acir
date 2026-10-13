{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0247 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00661 as MV00661
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02635 as MV02635
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02636 as MV02636
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02637 as MV02637
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02638 as MV02638
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X02 • K0247 ≈ K0247 • X27 • M2 • M7
proved = GL.•-cancelʳ {g = X02 • K0247} {g' = K0247 • X27 • M2 • M7} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02635.proved (MV00661.proved))) (trans (cong refl Base.proved) (move-product MV00661.proved (move-product MV02636.proved (move-product MV02637.proved (MV02638.proved))))))
