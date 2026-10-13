{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij02351467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00656 as MV00656
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02396 as MV02396
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0235 • K1467 ≈ K1467 • K0235
proved = GL.•-cancelʳ {g = K0235 • K1467} {g' = K1467 • K0235} {h = p (s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV00656.proved (MV02396.proved))) (trans (cong refl Base.proved) (move-product MV02396.proved (MV00656.proved))))
