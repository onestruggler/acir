{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01273456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00644 as MV00644
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02384 as MV02384
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0127 • K3456 ≈ K3456 • K0127
proved = GL.•-cancelʳ {g = K0127 • K3456} {g' = K3456 • K0127} {h = p (s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00644.proved (MV02384.proved))) (trans (cong refl Base.proved) (move-product MV02384.proved (MV00644.proved))))
