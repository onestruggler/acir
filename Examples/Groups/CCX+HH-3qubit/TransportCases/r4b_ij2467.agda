{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij2467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00703 as MV00703
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02950 as MV02950
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02951 as MV02951
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X46 • K2467 ≈ M2 • K2467 • M2 • K2467 • M2
proved = GL.•-cancelʳ {g = X46 • K2467} {g' = M2 • K2467 • M2 • K2467 • M2} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02950.proved (MV00703.proved))) (trans (cong refl Base.proved) (move-product MV02951.proved (move-product MV00703.proved (move-product MV02951.proved (move-product MV00703.proved (MV02951.proved)))))))
