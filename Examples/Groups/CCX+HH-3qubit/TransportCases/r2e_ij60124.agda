{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij60124 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02244 as MV02244
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02245 as MV02245
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M6 • K0124 ≈ K0124 • M6
proved = GL.•-cancelʳ {g = M6 • K0124} {g' = K0124 • M6} {h = p (s3 • s5 • s4)}
  (trans (sym (move-product MV02244.proved (MV02245.proved))) (trans (cong refl Base.proved) (move-product MV02245.proved (MV02244.proved))))
