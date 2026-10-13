{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij150246 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01285 as MV01285
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01286 as MV01286
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X15 • K0246 ≈ K0246 • X15
proved = GL.•-cancelʳ {g = X15 • K0246} {g' = K0246 • X15} {h = p (s1 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01285.proved (MV01286.proved))) (trans (cong refl Base.proved) (move-product MV01286.proved (MV01285.proved))))
