{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij260135 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01451 as MV01451
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01452 as MV01452
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X26 • K0135 ≈ K0135 • X26
proved = GL.•-cancelʳ {g = X26 • K0135} {g' = K0135 • X26} {h = p (s2 • s4 • s3 • s5)}
  (trans (sym (move-product MV01451.proved (MV01452.proved))) (trans (cong refl Base.proved) (move-product MV01452.proved (MV01451.proved))))
