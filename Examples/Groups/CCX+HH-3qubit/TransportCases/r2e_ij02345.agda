{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij02345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00695 as MV00695
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01919 as MV01919
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M0 • K2345 ≈ K2345 • M0
proved = GL.•-cancelʳ {g = M0 • K2345} {g' = K2345 • M0} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV01919.proved (MV00695.proved))) (trans (cong refl Base.proved) (move-product MV00695.proved (MV01919.proved))))
