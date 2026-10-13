{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij10 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01810 as MV01810
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01811 as MV01811
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M1 • M0 ≈ M0 • M1
proved = GL.•-cancelʳ {g = M1 • M0} {g' = M0 • M1} {h = p (s0 • s1 • s2 • s3)}
  (trans (sym (move-product MV01810.proved (MV01811.proved))) (trans (cong refl Base.proved) (move-product MV01811.proved (MV01810.proved))))
