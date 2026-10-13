{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50127 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02179 as MV02179
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02180 as MV02180
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M5 • K0127 ≈ K0127 • M5
proved = GL.•-cancelʳ {g = M5 • K0127} {g' = K0127 • M5} {h = p (s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02179.proved (MV02180.proved))) (trans (cong refl Base.proved) (move-product MV02180.proved (MV02179.proved))))
