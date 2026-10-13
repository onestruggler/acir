{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00656 as MV00656
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02616 as MV02616
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02978 as MV02978
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • K0235 ≈ K0235 • X25
proved = GL.•-cancelʳ {g = X35 • K0235} {g' = K0235 • X25} {h = p (s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV02978.proved (MV00656.proved))) (trans (cong refl Base.proved) (move-product MV00656.proved (MV02616.proved))))
