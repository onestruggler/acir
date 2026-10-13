{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij241 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00868 as MV00868
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00869 as MV00869
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • M1 ≈ M1 • X24
proved = GL.•-cancelʳ {g = X24 • M1} {g' = M1 • X24} {h = p (s0 • s1 • s3 • s2)}
  (trans (sym (move-product MV00868.proved (MV00869.proved))) (trans (cong refl Base.proved) (move-product MV00869.proved (MV00868.proved))))
