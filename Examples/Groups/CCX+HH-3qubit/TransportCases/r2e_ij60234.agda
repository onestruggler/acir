{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij60234 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02262 as MV02262
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02263 as MV02263
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M6 • K0234 ≈ K0234 • M6
proved = GL.•-cancelʳ {g = M6 • K0234} {g' = K0234 • M6} {h = p (s1 • s2 • s3 • s5 • s4)}
  (trans (sym (move-product MV02262.proved (MV02263.proved))) (trans (cong refl Base.proved) (move-product MV02263.proved (MV02262.proved))))
