{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij60125 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02246 as MV02246
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02247 as MV02247
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M6 • K0125 ≈ K0125 • M6
proved = GL.•-cancelʳ {g = M6 • K0125} {g' = K0125 • M6} {h = p (s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02246.proved (MV02247.proved))) (trans (cong refl Base.proved) (move-product MV02247.proved (MV02246.proved))))
