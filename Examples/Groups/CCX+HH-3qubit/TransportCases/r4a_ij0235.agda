{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00656 as MV00656
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02615 as MV02615
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02616 as MV02616
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02617 as MV02617
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02618 as MV02618
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X02 • K0235 ≈ K0235 • X25 • M2 • M5
proved = GL.•-cancelʳ {g = X02 • K0235} {g' = K0235 • X25 • M2 • M5} {h = p (s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV02615.proved (MV00656.proved))) (trans (cong refl Base.proved) (move-product MV00656.proved (move-product MV02616.proved (move-product MV02617.proved (MV02618.proved))))))
