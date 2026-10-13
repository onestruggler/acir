{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1236 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00677 as MV00677
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02898 as MV02898
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02899 as MV02899
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X23 • K1236 ≈ M1 • K1236 • M1 • K1236 • M1
proved = GL.•-cancelʳ {g = X23 • K1236} {g' = M1 • K1236 • M1 • K1236 • M1} {h = p (s0 • s1 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02898.proved (MV00677.proved))) (trans (cong refl Base.proved) (move-product MV02899.proved (move-product MV00677.proved (move-product MV02899.proved (move-product MV00677.proved (MV02899.proved)))))))
