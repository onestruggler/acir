{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01263457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00643 as MV00643
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02383 as MV02383
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0126 • K3457 ≈ K3457 • K0126
proved = GL.•-cancelʳ {g = K0126 • K3457} {g' = K3457 • K0126} {h = p (s5 • s4 • s3)}
  (trans (sym (move-product MV00643.proved (MV02383.proved))) (trans (cong refl Base.proved) (move-product MV02383.proved (MV00643.proved))))
