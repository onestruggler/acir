{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00694 as MV00694
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02767 as MV02767
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02768 as MV02768
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02769 as MV02769
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02770 as MV02770
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X15 • K1567 ≈ K1567 • X57 • M5 • M7
proved = GL.•-cancelʳ {g = X15 • K1567} {g' = K1567 • X57 • M5 • M7} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02767.proved (MV00694.proved))) (trans (cong refl Base.proved) (move-product MV00694.proved (move-product MV02768.proved (move-product MV02769.proved (MV02770.proved))))))
