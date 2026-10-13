{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij056 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00757 as MV00757
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00758 as MV00758
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X05 • M6 ≈ M6 • X05
proved = GL.•-cancelʳ {g = X05 • M6} {g' = M6 • X05} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00757.proved (MV00758.proved))) (trans (cong refl Base.proved) (move-product MV00758.proved (MV00757.proved))))
