{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij46 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01857 as MV01857
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01858 as MV01858
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M4 • M6 ≈ M6 • M4
proved = GL.•-cancelʳ {g = M4 • M6} {g' = M6 • M4} {h = p (s3 • s2 • s1 • s0 • s5 • s4)}
  (trans (sym (move-product MV01857.proved (MV01858.proved))) (trans (cong refl Base.proved) (move-product MV01858.proved (MV01857.proved))))
