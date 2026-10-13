{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0125 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00642 as MV00642
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02560 as MV02560
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02964 as MV02964
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X25 • K0125 ≈ K0125 • X15
proved = GL.•-cancelʳ {g = X25 • K0125} {g' = K0125 • X15} {h = p (s4 • s3)}
  (trans (sym (move-product MV02964.proved (MV00642.proved))) (trans (cong refl Base.proved) (move-product MV00642.proved (MV02560.proved))))
