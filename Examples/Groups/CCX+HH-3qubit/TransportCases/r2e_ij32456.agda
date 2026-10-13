{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij32456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02097 as MV02097
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02098 as MV02098
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M3 • K2456 ≈ K2456 • M3
proved = GL.•-cancelʳ {g = M3 • K2456} {g' = K2456 • M3} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02097.proved (MV02098.proved))) (trans (cong refl Base.proved) (move-product MV02098.proved (MV02097.proved))))
