{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij463 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00980 as MV00980
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00981 as MV00981
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X46 • M3 ≈ M3 • X46
proved = GL.•-cancelʳ {g = X46 • M3} {g' = M3 • X46} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00980.proved (MV00981.proved))) (trans (cong refl Base.proved) (move-product MV00981.proved (MV00980.proved))))
