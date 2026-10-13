{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij241356 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01410 as MV01410
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01411 as MV01411
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • K1356 ≈ K1356 • X24
proved = GL.•-cancelʳ {g = X24 • K1356} {g' = K1356 • X24} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01410.proved (MV01411.proved))) (trans (cong refl Base.proved) (move-product MV01411.proved (MV01410.proved))))
