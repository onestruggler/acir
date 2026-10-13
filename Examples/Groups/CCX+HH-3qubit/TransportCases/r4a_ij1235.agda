{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00676 as MV00676
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02695 as MV02695
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02696 as MV02696
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02697 as MV02697
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02698 as MV02698
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X12 • K1235 ≈ K1235 • X25 • M2 • M5
proved = GL.•-cancelʳ {g = X12 • K1235} {g' = K1235 • X25 • M2 • M5} {h = p (s0 • s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV02695.proved (MV00676.proved))) (trans (cong refl Base.proved) (move-product MV00676.proved (move-product MV02696.proved (move-product MV02697.proved (MV02698.proved))))))
