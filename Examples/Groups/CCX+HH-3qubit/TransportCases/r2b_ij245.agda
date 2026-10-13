{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij245 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00872 as MV00872
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00873 as MV00873
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • M5 ≈ M5 • X24
proved = GL.•-cancelʳ {g = X24 • M5} {g' = M5 • X24} {h = p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00872.proved (MV00873.proved))) (trans (cong refl Base.proved) (move-product MV00873.proved (MV00872.proved))))
