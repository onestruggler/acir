{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij62345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02302 as MV02302
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02303 as MV02303
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M6 • K2345 ≈ K2345 • M6
proved = GL.•-cancelʳ {g = M6 • K2345} {g' = K2345 • M6} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02302.proved (MV02303.proved))) (trans (cong refl Base.proved) (move-product MV02303.proved (MV02302.proved))))
