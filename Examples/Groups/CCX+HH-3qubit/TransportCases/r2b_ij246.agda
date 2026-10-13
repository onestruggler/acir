{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij246 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00874 as MV00874
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00875 as MV00875
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • M6 ≈ M6 • X24
proved = GL.•-cancelʳ {g = X24 • M6} {g' = M6 • X24} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00874.proved (MV00875.proved))) (trans (cong refl Base.proved) (move-product MV00875.proved (MV00874.proved))))
