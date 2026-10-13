{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij375 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00958 as MV00958
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00959 as MV00959
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X37 • M5 ≈ M5 • X37
proved = GL.•-cancelʳ {g = X37 • M5} {g' = M5 • X37} {h = p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00958.proved (MV00959.proved))) (trans (cong refl Base.proved) (move-product MV00959.proved (MV00958.proved))))
