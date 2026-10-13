{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij170235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01341 as MV01341
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01342 as MV01342
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X17 • K0235 ≈ K0235 • X17
proved = GL.•-cancelʳ {g = X17 • K0235} {g' = K0235 • X17} {h = p (s1 • s2 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01341.proved (MV01342.proved))) (trans (cong refl Base.proved) (move-product MV01342.proved (MV01341.proved))))
