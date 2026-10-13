{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij02471356 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00661 as MV00661
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02401 as MV02401
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0247 • K1356 ≈ K1356 • K0247
proved = GL.•-cancelʳ {g = K0247 • K1356} {g' = K1356 • K0247} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00661.proved (MV02401.proved))) (trans (cong refl Base.proved) (move-product MV02401.proved (MV00661.proved))))
