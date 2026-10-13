{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00672 as MV00672
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02679 as MV02679
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02680 as MV02680
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02681 as MV02681
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02682 as MV02682
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X04 • K0457 ≈ K0457 • X47 • M4 • M7
proved = GL.•-cancelʳ {g = X04 • K0457} {g' = K0457 • X47 • M4 • M7} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02679.proved (MV00672.proved))) (trans (cong refl Base.proved) (move-product MV00672.proved (move-product MV02680.proved (move-product MV02681.proved (MV02682.proved))))))
