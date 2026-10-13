{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij47 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01859 as MV01859
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01860 as MV01860
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M4 • M7 ≈ M7 • M4
proved = GL.•-cancelʳ {g = M4 • M7} {g' = M7 • M4} {h = p (s3 • s2 • s1 • s0 • s6 • s5 • s4)}
  (trans (sym (move-product MV01859.proved (MV01860.proved))) (trans (cong refl Base.proved) (move-product MV01860.proved (MV01859.proved))))
