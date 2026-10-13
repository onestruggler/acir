{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0367 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00670 as MV00670
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02672 as MV02672
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02992 as MV02992
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • K0367 ≈ K0367 • X37
proved = GL.•-cancelʳ {g = X67 • K0367} {g' = K0367 • X37} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02992.proved (MV00670.proved))) (trans (cong refl Base.proved) (move-product MV00670.proved (MV02672.proved))))
