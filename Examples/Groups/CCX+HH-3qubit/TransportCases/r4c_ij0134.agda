{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0134 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00645 as MV00645
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02572 as MV02572
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02967 as MV02967
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X34 • K0134 ≈ K0134 • X14
proved = GL.•-cancelʳ {g = X34 • K0134} {g' = K0134 • X14} {h = p (s2 • s3)}
  (trans (sym (move-product MV02967.proved (MV00645.proved))) (trans (cong refl Base.proved) (move-product MV00645.proved (MV02572.proved))))
