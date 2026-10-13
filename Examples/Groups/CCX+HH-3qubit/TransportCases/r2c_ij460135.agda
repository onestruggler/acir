{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij460135 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01657 as MV01657
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01658 as MV01658
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X46 • K0135 ≈ K0135 • X46
proved = GL.•-cancelʳ {g = X46 • K0135} {g' = K0135 • X46} {h = p (s2 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01657.proved (MV01658.proved))) (trans (cong refl Base.proved) (move-product MV01658.proved (MV01657.proved))))
