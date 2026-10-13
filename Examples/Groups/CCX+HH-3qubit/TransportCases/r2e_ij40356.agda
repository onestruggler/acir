{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40356 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02137 as MV02137
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02138 as MV02138
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M4 • K0356 ≈ K0356 • M4
proved = GL.•-cancelʳ {g = M4 • K0356} {g' = K0356 • M4} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02137.proved (MV02138.proved))) (trans (cong refl Base.proved) (move-product MV02138.proved (MV02137.proved))))
