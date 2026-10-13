{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij370 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00950 as MV00950
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00951 as MV00951
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X37 • M0 ≈ M0 • X37
proved = GL.•-cancelʳ {g = X37 • M0} {g' = M0 • X37} {h = p (s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00950.proved (MV00951.proved))) (trans (cong refl Base.proved) (move-product MV00951.proved (MV00950.proved))))
