{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij275 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00910 as MV00910
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00911 as MV00911
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X27 • M5 ≈ M5 • X27
proved = GL.•-cancelʳ {g = X27 • M5} {g' = M5 • X27} {h = p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00910.proved (MV00911.proved))) (trans (cong refl Base.proved) (move-product MV00911.proved (MV00910.proved))))
