{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1245 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00679 as MV00679
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02902 as MV02902
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02903 as MV02903
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • K1245 ≈ M1 • K1245 • M1 • K1245 • M1
proved = GL.•-cancelʳ {g = X24 • K1245} {g' = M1 • K1245 • M1 • K1245 • M1} {h = p (s0 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02902.proved (MV00679.proved))) (trans (cong refl Base.proved) (move-product MV02903.proved (move-product MV00679.proved (move-product MV02903.proved (move-product MV00679.proved (MV02903.proved)))))))
