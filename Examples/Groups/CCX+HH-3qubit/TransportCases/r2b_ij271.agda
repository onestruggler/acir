{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij271 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00904 as MV00904
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00905 as MV00905
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X27 • M1 ≈ M1 • X27
proved = GL.•-cancelʳ {g = X27 • M1} {g' = M1 • X27} {h = p (s0 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00904.proved (MV00905.proved))) (trans (cong refl Base.proved) (move-product MV00905.proved (MV00904.proved))))
