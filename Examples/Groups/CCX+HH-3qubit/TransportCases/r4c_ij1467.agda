{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00693 as MV00693
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02764 as MV02764
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03015 as MV03015
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • K1467 ≈ K1467 • X47
proved = GL.•-cancelʳ {g = X67 • K1467} {g' = K1467 • X47} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03015.proved (MV00693.proved))) (trans (cong refl Base.proved) (move-product MV00693.proved (MV02764.proved))))
