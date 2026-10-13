{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij76 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01898 as MV01898
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01899 as MV01899
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M7 • M6 ≈ M6 • M7
proved = GL.•-cancelʳ {g = M7 • M6} {g' = M6 • M7} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4)}
  (trans (sym (move-product MV01898.proved (MV01899.proved))) (trans (cong refl Base.proved) (move-product MV01899.proved (MV01898.proved))))
