{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij251346 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01439 as MV01439
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01440 as MV01440
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X25 • K1346 ≈ K1346 • X25
proved = GL.•-cancelʳ {g = X25 • K1346} {g' = K1346 • X25} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01439.proved (MV01440.proved))) (trans (cong refl Base.proved) (move-product MV01440.proved (MV01439.proved))))
