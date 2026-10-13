{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01234567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00641 as MV00641
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02381 as MV02381
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0123 • K4567 ≈ K4567 • K0123
proved = GL.•-cancelʳ {g = K0123 • K4567} {g' = K4567 • K0123} {h = p (ε)}
  (trans (sym (move-product MV00641.proved (MV02381.proved))) (trans (cong refl Base.proved) (move-product MV02381.proved (MV00641.proved))))
