{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0147 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00651 as MV00651
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02595 as MV02595
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02596 as MV02596
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02597 as MV02597
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02598 as MV02598
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X01 • K0147 ≈ K0147 • X17 • M1 • M7
proved = GL.•-cancelʳ {g = X01 • K0147} {g' = K0147 • X17 • M1 • M7} {h = p (s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02595.proved (MV00651.proved))) (trans (cong refl Base.proved) (move-product MV00651.proved (move-product MV02596.proved (move-product MV02597.proved (MV02598.proved))))))
