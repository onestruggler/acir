{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01472356 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00651 as MV00651
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02391 as MV02391
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0147 • K2356 ≈ K2356 • K0147
proved = GL.•-cancelʳ {g = K0147 • K2356} {g' = K2356 • K0147} {h = p (s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00651.proved (MV02391.proved))) (trans (cong refl Base.proved) (move-product MV02391.proved (MV00651.proved))))
