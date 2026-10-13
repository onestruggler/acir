{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij61457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02300 as MV02300
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02301 as MV02301
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M6 • K1457 ≈ K1457 • M6
proved = GL.•-cancelʳ {g = M6 • K1457} {g' = K1457 • M6} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02300.proved (MV02301.proved))) (trans (cong refl Base.proved) (move-product MV02301.proved (MV02300.proved))))
