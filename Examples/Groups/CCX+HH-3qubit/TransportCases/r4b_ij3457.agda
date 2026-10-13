{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij3457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00706 as MV00706
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02956 as MV02956
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02957 as MV02957
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K3457 ≈ M3 • K3457 • M3 • K3457 • M3
proved = GL.•-cancelʳ {g = X45 • K3457} {g' = M3 • K3457 • M3 • K3457 • M3} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02956.proved (MV00706.proved))) (trans (cong refl Base.proved) (move-product MV02957.proved (move-product MV00706.proved (move-product MV02957.proved (move-product MV00706.proved (MV02957.proved)))))))
