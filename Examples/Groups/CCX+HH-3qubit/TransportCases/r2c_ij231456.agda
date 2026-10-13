{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij231456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01383 as MV01383
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01384 as MV01384
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X23 • K1456 ≈ K1456 • X23
proved = GL.•-cancelʳ {g = X23 • K1456} {g' = K1456 • X23} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01383.proved (MV01384.proved))) (trans (cong refl Base.proved) (move-product MV01384.proved (MV01383.proved))))
