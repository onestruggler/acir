{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1236 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00677 as MV00677
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02699 as MV02699
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02700 as MV02700
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02701 as MV02701
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02702 as MV02702
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X12 • K1236 ≈ K1236 • X26 • M2 • M6
proved = GL.•-cancelʳ {g = X12 • K1236} {g' = K1236 • X26 • M2 • M6} {h = p (s0 • s1 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02699.proved (MV00677.proved))) (trans (cong refl Base.proved) (move-product MV00677.proved (move-product MV02700.proved (move-product MV02701.proved (MV02702.proved))))))
