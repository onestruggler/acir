{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij70134 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02319 as MV02319
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02320 as MV02320
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M7 • K0134 ≈ K0134 • M7
proved = GL.•-cancelʳ {g = M7 • K0134} {g' = K0134 • M7} {h = p (s2 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02319.proved (MV02320.proved))) (trans (cong refl Base.proved) (move-product MV02320.proved (MV02319.proved))))
