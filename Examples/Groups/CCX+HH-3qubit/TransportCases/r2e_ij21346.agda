{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij21346 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02014 as MV02014
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02015 as MV02015
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M2 • K1346 ≈ K1346 • M2
proved = GL.•-cancelʳ {g = M2 • K1346} {g' = K1346 • M2} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02014.proved (MV02015.proved))) (trans (cong refl Base.proved) (move-product MV02015.proved (MV02014.proved))))
