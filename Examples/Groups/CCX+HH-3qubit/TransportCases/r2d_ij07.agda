{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij07 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01808 as MV01808
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01809 as MV01809
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M0 • M7 ≈ M7 • M0
proved = GL.•-cancelʳ {g = M0 • M7} {g' = M7 • M0} {h = p (s6 • s5 • s4)}
  (trans (sym (move-product MV01808.proved (MV01809.proved))) (trans (cong refl Base.proved) (move-product MV01809.proved (MV01808.proved))))
