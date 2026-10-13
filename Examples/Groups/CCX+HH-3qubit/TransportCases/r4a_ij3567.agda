{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij3567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00708 as MV00708
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02823 as MV02823
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02824 as MV02824
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02825 as MV02825
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02826 as MV02826
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • K3567 ≈ K3567 • X57 • M5 • M7
proved = GL.•-cancelʳ {g = X35 • K3567} {g' = K3567 • X57 • M5 • M7} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02823.proved (MV00708.proved))) (trans (cong refl Base.proved) (move-product MV00708.proved (move-product MV02824.proved (move-product MV02825.proved (MV02826.proved))))))
