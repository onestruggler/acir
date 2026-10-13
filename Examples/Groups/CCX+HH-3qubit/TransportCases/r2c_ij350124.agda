{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij350124 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00209 as MV00209
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as MV00245
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • K0124 ≈ K0124 • X35
proved = GL.•-cancelʳ {g = X35 • K0124} {g' = K0124 • X35} {h = p (s3)}
  (trans (sym (move-product MV00209.proved (MV00245.proved))) (trans (cong refl Base.proved) (move-product MV00245.proved (MV00209.proved))))
