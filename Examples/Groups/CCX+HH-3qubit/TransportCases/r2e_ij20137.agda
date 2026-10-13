{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20137 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00648 as MV00648
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01985 as MV01985
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M2 • K0137 ≈ K0137 • M2
proved = GL.•-cancelʳ {g = M2 • K0137} {g' = K0137 • M2} {h = p (s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01985.proved (MV00648.proved))) (trans (cong refl Base.proved) (move-product MV00648.proved (MV01985.proved))))
