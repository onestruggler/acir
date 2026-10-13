{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij072346 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01201 as MV01201
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01202 as MV01202
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X07 • K2346 ≈ K2346 • X07
proved = GL.•-cancelʳ {g = X07 • K2346} {g' = K2346 • X07} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01201.proved (MV01202.proved))) (trans (cong refl Base.proved) (move-product MV01202.proved (MV01201.proved))))
