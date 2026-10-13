{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij70125 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02315 as MV02315
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02316 as MV02316
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M7 • K0125 ≈ K0125 • M7
proved = GL.•-cancelʳ {g = M7 • K0125} {g' = K0125 • M7} {h = p (s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02315.proved (MV02316.proved))) (trans (cong refl Base.proved) (move-product MV02316.proved (MV02315.proved))))
