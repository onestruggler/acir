{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij2345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00695 as MV00695
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02934 as MV02934
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02935 as MV02935
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X34 • K2345 ≈ M2 • K2345 • M2 • K2345 • M2
proved = GL.•-cancelʳ {g = X34 • K2345} {g' = M2 • K2345 • M2 • K2345 • M2} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02934.proved (MV00695.proved))) (trans (cong refl Base.proved) (move-product MV02935.proved (move-product MV00695.proved (move-product MV02935.proved (move-product MV00695.proved (MV02935.proved)))))))
