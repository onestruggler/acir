{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij261 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00892 as MV00892
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00893 as MV00893
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X26 • M1 ≈ M1 • X26
proved = GL.•-cancelʳ {g = X26 • M1} {g' = M1 • X26} {h = p (s0 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00892.proved (MV00893.proved))) (trans (cong refl Base.proved) (move-product MV00893.proved (MV00892.proved))))
