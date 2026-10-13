{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0135 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00646 as MV00646
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02576 as MV02576
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02968 as MV02968
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • K0135 ≈ K0135 • X15
proved = GL.•-cancelʳ {g = X35 • K0135} {g' = K0135 • X15} {h = p (s2 • s4 • s3)}
  (trans (sym (move-product MV02968.proved (MV00646.proved))) (trans (cong refl Base.proved) (move-product MV00646.proved (MV02576.proved))))
