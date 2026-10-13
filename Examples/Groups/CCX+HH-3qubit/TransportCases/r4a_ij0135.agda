{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0135 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00646 as MV00646
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02575 as MV02575
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02576 as MV02576
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02577 as MV02577
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02578 as MV02578
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X01 • K0135 ≈ K0135 • X15 • M1 • M5
proved = GL.•-cancelʳ {g = X01 • K0135} {g' = K0135 • X15 • M1 • M5} {h = p (s2 • s4 • s3)}
  (trans (sym (move-product MV02575.proved (MV00646.proved))) (trans (cong refl Base.proved) (move-product MV00646.proved (move-product MV02576.proved (move-product MV02577.proved (MV02578.proved))))))
