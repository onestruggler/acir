{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij264 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00896 as MV00896
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00897 as MV00897
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X26 • M4 ≈ M4 • X26
proved = GL.•-cancelʳ {g = X26 • M4} {g' = M4 • X26} {h = p (s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00896.proved (MV00897.proved))) (trans (cong refl Base.proved) (move-product MV00897.proved (MV00896.proved))))
