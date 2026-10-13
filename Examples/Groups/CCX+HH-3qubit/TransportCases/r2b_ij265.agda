{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij265 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00898 as MV00898
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00899 as MV00899
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X26 • M5 ≈ M5 • X26
proved = GL.•-cancelʳ {g = X26 • M5} {g' = M5 • X26} {h = p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00898.proved (MV00899.proved))) (trans (cong refl Base.proved) (move-product MV00899.proved (MV00898.proved))))
