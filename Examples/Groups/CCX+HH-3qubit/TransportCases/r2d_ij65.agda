{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij65 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01883 as MV01883
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01884 as MV01884
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M6 • M5 ≈ M5 • M6
proved = GL.•-cancelʳ {g = M6 • M5} {g' = M5 • M6} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4)}
  (trans (sym (move-product MV01883.proved (MV01884.proved))) (trans (cong refl Base.proved) (move-product MV01884.proved (MV01883.proved))))
