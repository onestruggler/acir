{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij126 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00792 as MV00792
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00793 as MV00793
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X12 • M6 ≈ M6 • X12
proved = GL.•-cancelʳ {g = X12 • M6} {g' = M6 • X12} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2)}
  (trans (sym (move-product MV00792.proved (MV00793.proved))) (trans (cong refl Base.proved) (move-product MV00793.proved (MV00792.proved))))
