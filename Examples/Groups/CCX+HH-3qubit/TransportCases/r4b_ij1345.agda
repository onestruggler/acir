{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00685 as MV00685
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02914 as MV02914
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02915 as MV02915
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X34 • K1345 ≈ M1 • K1345 • M1 • K1345 • M1
proved = GL.•-cancelʳ {g = X34 • K1345} {g' = M1 • K1345 • M1 • K1345 • M1} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02914.proved (MV00685.proved))) (trans (cong refl Base.proved) (move-product MV02915.proved (move-product MV00685.proved (move-product MV02915.proved (move-product MV00685.proved (MV02915.proved)))))))
