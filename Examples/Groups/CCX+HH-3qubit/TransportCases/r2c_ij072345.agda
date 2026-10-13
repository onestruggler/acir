{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij072345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01199 as MV01199
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01200 as MV01200
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X07 • K2345 ≈ K2345 • X07
proved = GL.•-cancelʳ {g = X07 • K2345} {g' = K2345 • X07} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01199.proved (MV01200.proved))) (trans (cong refl Base.proved) (move-product MV01200.proved (MV01199.proved))))
