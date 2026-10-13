{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0125 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00642 as MV00642
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02559 as MV02559
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02560 as MV02560
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02561 as MV02561
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02562 as MV02562
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X01 • K0125 ≈ K0125 • X15 • M1 • M5
proved = GL.•-cancelʳ {g = X01 • K0125} {g' = K0125 • X15 • M1 • M5} {h = p (s4 • s3)}
  (trans (sym (move-product MV02559.proved (MV00642.proved))) (trans (cong refl Base.proved) (move-product MV00642.proved (move-product MV02560.proved (move-product MV02561.proved (MV02562.proved))))))
