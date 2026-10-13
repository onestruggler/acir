{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0245 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00659 as MV00659
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02628 as MV02628
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02981 as MV02981
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K0245 ≈ K0245 • X25
proved = GL.•-cancelʳ {g = X45 • K0245} {g' = K0245 • X25} {h = p (s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02981.proved (MV00659.proved))) (trans (cong refl Base.proved) (move-product MV00659.proved (MV02628.proved))))
