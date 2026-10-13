{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0136 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00647 as MV00647
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02840 as MV02840
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02841 as MV02841
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X13 • K0136 ≈ M0 • K0136 • M0 • K0136 • M0
proved = GL.•-cancelʳ {g = X13 • K0136} {g' = M0 • K0136 • M0 • K0136 • M0} {h = p (s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02840.proved (MV00647.proved))) (trans (cong refl Base.proved) (move-product MV02841.proved (move-product MV00647.proved (move-product MV02841.proved (move-product MV00647.proved (MV02841.proved)))))))
