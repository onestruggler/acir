{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij31457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02091 as MV02091
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02092 as MV02092
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M3 • K1457 ≈ K1457 • M3
proved = GL.•-cancelʳ {g = M3 • K1457} {g' = K1457 • M3} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02091.proved (MV02092.proved))) (trans (cong refl Base.proved) (move-product MV02092.proved (MV02091.proved))))
