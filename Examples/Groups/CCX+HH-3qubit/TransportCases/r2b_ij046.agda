{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij046 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00745 as MV00745
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00746 as MV00746
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X04 • M6 ≈ M6 • X04
proved = GL.•-cancelʳ {g = X04 • M6} {g' = M6 • X04} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2)}
  (trans (sym (move-product MV00745.proved (MV00746.proved))) (trans (cong refl Base.proved) (move-product MV00746.proved (MV00745.proved))))
