{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij23450167 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00695 as MV00695
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02435 as MV02435
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K2345 • K0167 ≈ K0167 • K2345
proved = GL.•-cancelʳ {g = K2345 • K0167} {g' = K0167 • K2345} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV00695.proved (MV02435.proved))) (trans (cong refl Base.proved) (move-product MV02435.proved (MV00695.proved))))
