{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1357 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00689 as MV00689
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02922 as MV02922
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02923 as MV02923
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • K1357 ≈ M1 • K1357 • M1 • K1357 • M1
proved = GL.•-cancelʳ {g = X35 • K1357} {g' = M1 • K1357 • M1 • K1357 • M1} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02922.proved (MV00689.proved))) (trans (cong refl Base.proved) (move-product MV02923.proved (move-product MV00689.proved (move-product MV02923.proved (move-product MV00689.proved (MV02923.proved)))))))
