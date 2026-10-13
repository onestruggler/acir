{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij01235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00676 as MV00676
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01900 as MV01900
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M0 • K1235 ≈ K1235 • M0
proved = GL.•-cancelʳ {g = M0 • K1235} {g' = K1235 • M0} {h = p (s0 • s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV01900.proved (MV00676.proved))) (trans (cong refl Base.proved) (move-product MV00676.proved (MV01900.proved))))
