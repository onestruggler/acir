{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij370124 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01594 as MV01594
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01595 as MV01595
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X37 • K0124 ≈ K0124 • X37
proved = GL.•-cancelʳ {g = X37 • K0124} {g' = K0124 • X37} {h = p (s3 • s6 • s5)}
  (trans (sym (move-product MV01594.proved (MV01595.proved))) (trans (cong refl Base.proved) (move-product MV01595.proved (MV01594.proved))))
