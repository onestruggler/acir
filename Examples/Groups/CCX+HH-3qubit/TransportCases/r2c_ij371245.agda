{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij371245 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01614 as MV01614
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01615 as MV01615
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X37 • K1245 ≈ K1245 • X37
proved = GL.•-cancelʳ {g = X37 • K1245} {g' = K1245 • X37} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01614.proved (MV01615.proved))) (trans (cong refl Base.proved) (move-product MV01615.proved (MV01614.proved))))
