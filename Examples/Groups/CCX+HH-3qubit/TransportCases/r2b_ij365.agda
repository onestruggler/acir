{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij365 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00946 as MV00946
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00947 as MV00947
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X36 • M5 ≈ M5 • X36
proved = GL.•-cancelʳ {g = X36 • M5} {g' = M5 • X36} {h = p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00946.proved (MV00947.proved))) (trans (cong refl Base.proved) (move-product MV00947.proved (MV00946.proved))))
