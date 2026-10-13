{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20135 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00646 as MV00646
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01983 as MV01983
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M2 • K0135 ≈ K0135 • M2
proved = GL.•-cancelʳ {g = M2 • K0135} {g' = K0135 • M2} {h = p (s2 • s4 • s3)}
  (trans (sym (move-product MV01983.proved (MV00646.proved))) (trans (cong refl Base.proved) (move-product MV00646.proved (MV01983.proved))))
