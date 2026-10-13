{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij125 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00790 as MV00790
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00791 as MV00791
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X12 • M5 ≈ M5 • X12
proved = GL.•-cancelʳ {g = X12 • M5} {g' = M5 • X12} {h = p (s4 • s3 • s2 • s1 • s0 • s1 • s2)}
  (trans (sym (move-product MV00790.proved (MV00791.proved))) (trans (cong refl Base.proved) (move-product MV00791.proved (MV00790.proved))))
