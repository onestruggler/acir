{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij240156 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01396 as MV01396
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01397 as MV01397
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • K0156 ≈ K0156 • X24
proved = GL.•-cancelʳ {g = X24 • K0156} {g' = K0156 • X24} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01396.proved (MV01397.proved))) (trans (cong refl Base.proved) (move-product MV01397.proved (MV01396.proved))))
