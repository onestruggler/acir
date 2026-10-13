{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij2367 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00700 as MV00700
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02792 as MV02792
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03022 as MV03022
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • K2367 ≈ K2367 • X37
proved = GL.•-cancelʳ {g = X67 • K2367} {g' = K2367 • X37} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03022.proved (MV00700.proved))) (trans (cong refl Base.proved) (move-product MV00700.proved (MV02792.proved))))
