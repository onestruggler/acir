{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij371456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01620 as MV01620
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01621 as MV01621
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X37 • K1456 ≈ K1456 • X37
proved = GL.•-cancelʳ {g = X37 • K1456} {g' = K1456 • X37} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01620.proved (MV01621.proved))) (trans (cong refl Base.proved) (move-product MV01621.proved (MV01620.proved))))
