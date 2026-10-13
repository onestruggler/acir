{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00673 as MV00673
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02683 as MV02683
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02684 as MV02684
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02685 as MV02685
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02686 as MV02686
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X04 • K0467 ≈ K0467 • X47 • M4 • M7
proved = GL.•-cancelʳ {g = X04 • K0467} {g' = K0467 • X47 • M4 • M7} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02683.proved (MV00673.proved))) (trans (cong refl Base.proved) (move-product MV00673.proved (move-product MV02684.proved (move-product MV02685.proved (MV02686.proved))))))
