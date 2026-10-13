{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01352467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00646 as MV00646
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02386 as MV02386
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0135 • K2467 ≈ K2467 • K0135
proved = GL.•-cancelʳ {g = K0135 • K2467} {g' = K2467 • K0135} {h = p (s2 • s4 • s3)}
  (trans (sym (move-product MV00646.proved (MV02386.proved))) (trans (cong refl Base.proved) (move-product MV02386.proved (MV00646.proved))))
