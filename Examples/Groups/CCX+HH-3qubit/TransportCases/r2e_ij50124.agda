{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50124 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02175 as MV02175
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02176 as MV02176
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M5 • K0124 ≈ K0124 • M5
proved = GL.•-cancelʳ {g = M5 • K0124} {g' = K0124 • M5} {h = p (s3 • s4)}
  (trans (sym (move-product MV02175.proved (MV02176.proved))) (trans (cong refl Base.proved) (move-product MV02176.proved (MV02175.proved))))
