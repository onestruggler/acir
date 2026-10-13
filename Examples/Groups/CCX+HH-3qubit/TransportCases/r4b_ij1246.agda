{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1246 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00680 as MV00680
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02904 as MV02904
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02905 as MV02905
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • K1246 ≈ M1 • K1246 • M1 • K1246 • M1
proved = GL.•-cancelʳ {g = X24 • K1246} {g' = M1 • K1246 • M1 • K1246 • M1} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02904.proved (MV00680.proved))) (trans (cong refl Base.proved) (move-product MV02905.proved (move-product MV00680.proved (move-product MV02905.proved (move-product MV00680.proved (MV02905.proved)))))))
