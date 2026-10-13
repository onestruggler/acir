{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij62347 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02304 as MV02304
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02305 as MV02305
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M6 • K2347 ≈ K2347 • M6
proved = GL.•-cancelʳ {g = M6 • K2347} {g' = K2347 • M6} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02304.proved (MV02305.proved))) (trans (cong refl Base.proved) (move-product MV02305.proved (MV02304.proved))))
