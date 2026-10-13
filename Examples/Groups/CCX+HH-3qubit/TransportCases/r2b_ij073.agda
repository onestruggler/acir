{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij073 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00777 as MV00777
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00778 as MV00778
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X07 • M3 ≈ M3 • X07
proved = GL.•-cancelʳ {g = X07 • M3} {g' = M3 • X07} {h = p (s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00777.proved (MV00778.proved))) (trans (cong refl Base.proved) (move-product MV00778.proved (MV00777.proved))))
