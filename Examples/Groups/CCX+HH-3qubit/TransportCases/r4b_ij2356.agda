{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij2356 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00698 as MV00698
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02940 as MV02940
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02941 as MV02941
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • K2356 ≈ M2 • K2356 • M2 • K2356 • M2
proved = GL.•-cancelʳ {g = X35 • K2356} {g' = M2 • K2356 • M2 • K2356 • M2} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02940.proved (MV00698.proved))) (trans (cong refl Base.proved) (move-product MV02941.proved (move-product MV00698.proved (move-product MV02941.proved (move-product MV00698.proved (MV02941.proved)))))))
