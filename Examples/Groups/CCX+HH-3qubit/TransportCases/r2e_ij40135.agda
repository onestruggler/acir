{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40135 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02113 as MV02113
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02114 as MV02114
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M4 • K0135 ≈ K0135 • M4
proved = GL.•-cancelʳ {g = M4 • K0135} {g' = K0135 • M4} {h = p (s2 • s4 • s3 • s4)}
  (trans (sym (move-product MV02113.proved (MV02114.proved))) (trans (cong refl Base.proved) (move-product MV02114.proved (MV02113.proved))))
