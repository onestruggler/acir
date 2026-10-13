{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij60345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02274 as MV02274
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02275 as MV02275
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M6 • K0345 ≈ K0345 • M6
proved = GL.•-cancelʳ {g = M6 • K0345} {g' = K0345 • M6} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02274.proved (MV02275.proved))) (trans (cong refl Base.proved) (move-product MV02275.proved (MV02274.proved))))
