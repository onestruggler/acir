{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij071235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01181 as MV01181
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01182 as MV01182
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X07 • K1235 ≈ K1235 • X07
proved = GL.•-cancelʳ {g = X07 • K1235} {g' = K1235 • X07} {h = p (s0 • s1 • s2 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01181.proved (MV01182.proved))) (trans (cong refl Base.proved) (move-product MV01182.proved (MV01181.proved))))
