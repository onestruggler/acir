{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij460127 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01655 as MV01655
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01656 as MV01656
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X46 • K0127 ≈ K0127 • X46
proved = GL.•-cancelʳ {g = X46 • K0127} {g' = K0127 • X46} {h = p (s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01655.proved (MV01656.proved))) (trans (cong refl Base.proved) (move-product MV01656.proved (MV01655.proved))))
