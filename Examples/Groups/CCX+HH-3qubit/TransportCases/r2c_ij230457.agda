{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij230457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01377 as MV01377
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01378 as MV01378
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X23 • K0457 ≈ K0457 • X23
proved = GL.•-cancelʳ {g = X23 • K0457} {g' = K0457 • X23} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01377.proved (MV01378.proved))) (trans (cong refl Base.proved) (move-product MV01378.proved (MV01377.proved))))
