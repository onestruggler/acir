{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij60127 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02248 as MV02248
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02249 as MV02249
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M6 • K0127 ≈ K0127 • M6
proved = GL.•-cancelʳ {g = M6 • K0127} {g' = K0127 • M6} {h = p (s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02248.proved (MV02249.proved))) (trans (cong refl Base.proved) (move-product MV02249.proved (MV02248.proved))))
