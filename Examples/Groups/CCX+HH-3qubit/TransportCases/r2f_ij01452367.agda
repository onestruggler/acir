{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01452367 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00649 as MV00649
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02389 as MV02389
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0145 • K2367 ≈ K2367 • K0145
proved = GL.•-cancelʳ {g = K0145 • K2367} {g' = K2367 • K0145} {h = p (s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV00649.proved (MV02389.proved))) (trans (cong refl Base.proved) (move-product MV02389.proved (MV00649.proved))))
