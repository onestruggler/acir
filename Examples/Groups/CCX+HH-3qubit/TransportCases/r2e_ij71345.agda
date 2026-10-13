{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij71345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02363 as MV02363
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02364 as MV02364
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M7 • K1345 ≈ K1345 • M7
proved = GL.•-cancelʳ {g = M7 • K1345} {g' = K1345 • M7} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02363.proved (MV02364.proved))) (trans (cong refl Base.proved) (move-product MV02364.proved (MV02363.proved))))
