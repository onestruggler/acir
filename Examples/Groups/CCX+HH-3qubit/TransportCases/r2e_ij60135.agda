{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij60135 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02252 as MV02252
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02253 as MV02253
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M6 • K0135 ≈ K0135 • M6
proved = GL.•-cancelʳ {g = M6 • K0135} {g' = K0135 • M6} {h = p (s2 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02252.proved (MV02253.proved))) (trans (cong refl Base.proved) (move-product MV02253.proved (MV02252.proved))))
