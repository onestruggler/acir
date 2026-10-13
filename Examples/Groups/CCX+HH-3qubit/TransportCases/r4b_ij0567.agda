{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00674 as MV00674
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02893 as MV02893
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02894 as MV02894
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • K0567 ≈ M0 • K0567 • M0 • K0567 • M0
proved = GL.•-cancelʳ {g = X56 • K0567} {g' = M0 • K0567 • M0 • K0567 • M0} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02893.proved (MV00674.proved))) (trans (cong refl Base.proved) (move-product MV02894.proved (move-product MV00674.proved (move-product MV02894.proved (move-product MV00674.proved (MV02894.proved)))))))
