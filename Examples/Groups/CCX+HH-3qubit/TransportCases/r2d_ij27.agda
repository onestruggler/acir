{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij27 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01833 as MV01833
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01834 as MV01834
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M2 • M7 ≈ M7 • M2
proved = GL.•-cancelʳ {g = M2 • M7} {g' = M7 • M2} {h = p (s1 • s0 • s6 • s5 • s4)}
  (trans (sym (move-product MV01833.proved (MV01834.proved))) (trans (cong refl Base.proved) (move-product MV01834.proved (MV01833.proved))))
