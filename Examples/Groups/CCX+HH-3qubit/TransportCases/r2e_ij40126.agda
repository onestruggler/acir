{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40126 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02109 as MV02109
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02110 as MV02110
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M4 • K0126 ≈ K0126 • M4
proved = GL.•-cancelʳ {g = M4 • K0126} {g' = K0126 • M4} {h = p (s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02109.proved (MV02110.proved))) (trans (cong refl Base.proved) (move-product MV02110.proved (MV02109.proved))))
