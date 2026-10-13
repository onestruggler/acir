{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij3457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00706 as MV00706
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02815 as MV02815
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02816 as MV02816
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02817 as MV02817
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02818 as MV02818
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X34 • K3457 ≈ K3457 • X47 • M4 • M7
proved = GL.•-cancelʳ {g = X34 • K3457} {g' = K3457 • X47 • M4 • M7} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02815.proved (MV00706.proved))) (trans (cong refl Base.proved) (move-product MV00706.proved (move-product MV02816.proved (move-product MV02817.proved (MV02818.proved))))))
