{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij06 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01806 as MV01806
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01807 as MV01807
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M0 • M6 ≈ M6 • M0
proved = GL.•-cancelʳ {g = M0 • M6} {g' = M6 • M0} {h = p (s5 • s4)}
  (trans (sym (move-product MV01806.proved (MV01807.proved))) (trans (cong refl Base.proved) (move-product MV01807.proved (MV01806.proved))))
