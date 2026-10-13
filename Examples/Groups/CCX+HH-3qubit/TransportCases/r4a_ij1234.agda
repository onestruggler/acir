{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1234 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00675 as MV00675
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02691 as MV02691
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02692 as MV02692
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02693 as MV02693
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02694 as MV02694
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X12 • K1234 ≈ K1234 • X24 • M2 • M4
proved = GL.•-cancelʳ {g = X12 • K1234} {g' = K1234 • X24 • M2 • M4} {h = p (s0 • s1 • s2 • s3)}
  (trans (sym (move-product MV02691.proved (MV00675.proved))) (trans (cong refl Base.proved) (move-product MV00675.proved (move-product MV02692.proved (move-product MV02693.proved (MV02694.proved))))))
