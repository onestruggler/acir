{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij150236 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01281 as MV01281
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01282 as MV01282
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X15 • K0236 ≈ K0236 • X15
proved = GL.•-cancelʳ {g = X15 • K0236} {g' = K0236 • X15} {h = p (s1 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01281.proved (MV01282.proved))) (trans (cong refl Base.proved) (move-product MV01282.proved (MV01281.proved))))
