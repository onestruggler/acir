{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij071245 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01185 as MV01185
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01186 as MV01186
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X07 • K1245 ≈ K1245 • X07
proved = GL.•-cancelʳ {g = X07 • K1245} {g' = K1245 • X07} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01185.proved (MV01186.proved))) (trans (cong refl Base.proved) (move-product MV01186.proved (MV01185.proved))))
