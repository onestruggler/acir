{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00665 as MV00665
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02652 as MV02652
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02987 as MV02987
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K0345 ≈ K0345 • X35
proved = GL.•-cancelʳ {g = X45 • K0345} {g' = K0345 • X35} {h = p (s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02987.proved (MV00665.proved))) (trans (cong refl Base.proved) (move-product MV00665.proved (MV02652.proved))))
