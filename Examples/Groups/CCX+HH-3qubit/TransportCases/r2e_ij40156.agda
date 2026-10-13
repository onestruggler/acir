{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40156 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02119 as MV02119
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02120 as MV02120
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M4 • K0156 ≈ K0156 • M4
proved = GL.•-cancelʳ {g = M4 • K0156} {g' = K0156 • M4} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02119.proved (MV02120.proved))) (trans (cong refl Base.proved) (move-product MV02120.proved (MV02119.proved))))
