{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01372456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00648 as MV00648
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02388 as MV02388
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0137 • K2456 ≈ K2456 • K0137
proved = GL.•-cancelʳ {g = K0137 • K2456} {g' = K2456 • K0137} {h = p (s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00648.proved (MV02388.proved))) (trans (cong refl Base.proved) (move-product MV02388.proved (MV00648.proved))))
