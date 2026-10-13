{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij23470156 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00697 as MV00697
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02437 as MV02437
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K2347 • K0156 ≈ K0156 • K2347
proved = GL.•-cancelʳ {g = K2347 • K0156} {g' = K0156 • K2347} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00697.proved (MV02437.proved))) (trans (cong refl Base.proved) (move-product MV02437.proved (MV00697.proved))))
