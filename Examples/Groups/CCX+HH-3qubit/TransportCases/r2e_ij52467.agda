{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij52467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02239 as MV02239
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02240 as MV02240
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M5 • K2467 ≈ K2467 • M5
proved = GL.•-cancelʳ {g = M5 • K2467} {g' = K2467 • M5} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02239.proved (MV02240.proved))) (trans (cong refl Base.proved) (move-product MV02240.proved (MV02239.proved))))
