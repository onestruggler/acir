{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0145 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00649 as MV00649
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02588 as MV02588
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02971 as MV02971
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K0145 ≈ K0145 • X15
proved = GL.•-cancelʳ {g = X45 • K0145} {g' = K0145 • X15} {h = p (s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02971.proved (MV00649.proved))) (trans (cong refl Base.proved) (move-product MV00649.proved (MV02588.proved))))
