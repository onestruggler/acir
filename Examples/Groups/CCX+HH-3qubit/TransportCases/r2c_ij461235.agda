{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij461235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01671 as MV01671
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01672 as MV01672
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X46 • K1235 ≈ K1235 • X46
proved = GL.•-cancelʳ {g = X46 • K1235} {g' = K1235 • X46} {h = p (s0 • s1 • s2 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01671.proved (MV01672.proved))) (trans (cong refl Base.proved) (move-product MV01672.proved (MV01671.proved))))
