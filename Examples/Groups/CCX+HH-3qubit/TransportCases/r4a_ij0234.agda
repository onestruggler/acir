{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0234 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00655 as MV00655
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02611 as MV02611
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02612 as MV02612
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02613 as MV02613
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02614 as MV02614
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X02 • K0234 ≈ K0234 • X24 • M2 • M4
proved = GL.•-cancelʳ {g = X02 • K0234} {g' = K0234 • X24 • M2 • M4} {h = p (s1 • s2 • s3)}
  (trans (sym (move-product MV02611.proved (MV00655.proved))) (trans (cong refl Base.proved) (move-product MV00655.proved (move-product MV02612.proved (move-product MV02613.proved (MV02614.proved))))))
