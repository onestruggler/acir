{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij13450267 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00685 as MV00685
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02425 as MV02425
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K1345 • K0267 ≈ K0267 • K1345
proved = GL.•-cancelʳ {g = K1345 • K0267} {g' = K0267 • K1345} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV00685.proved (MV02425.proved))) (trans (cong refl Base.proved) (move-product MV02425.proved (MV00685.proved))))
