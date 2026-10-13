{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1237 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00678 as MV00678
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02703 as MV02703
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02704 as MV02704
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02705 as MV02705
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02706 as MV02706
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X12 • K1237 ≈ K1237 • X27 • M2 • M7
proved = GL.•-cancelʳ {g = X12 • K1237} {g' = K1237 • X27 • M2 • M7} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02703.proved (MV00678.proved))) (trans (cong refl Base.proved) (move-product MV00678.proved (move-product MV02704.proved (move-product MV02705.proved (MV02706.proved))))))
