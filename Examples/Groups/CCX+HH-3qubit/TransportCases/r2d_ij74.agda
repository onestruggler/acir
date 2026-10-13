{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij74 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01894 as MV01894
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01895 as MV01895
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M7 • M4 ≈ M4 • M7
proved = GL.•-cancelʳ {g = M7 • M4} {g' = M4 • M7} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4)}
  (trans (sym (move-product MV01894.proved (MV01895.proved))) (trans (cong refl Base.proved) (move-product MV01895.proved (MV01894.proved))))
