{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij70136 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02323 as MV02323
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02324 as MV02324
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M7 • K0136 ≈ K0136 • M7
proved = GL.•-cancelʳ {g = M7 • K0136} {g' = K0136 • M7} {h = p (s2 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02323.proved (MV02324.proved))) (trans (cong refl Base.proved) (move-product MV02324.proved (MV02323.proved))))
