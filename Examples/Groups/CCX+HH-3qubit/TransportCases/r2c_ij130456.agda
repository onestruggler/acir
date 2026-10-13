{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij130456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01235 as MV01235
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01236 as MV01236
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X13 • K0456 ≈ K0456 • X13
proved = GL.•-cancelʳ {g = X13 • K0456} {g' = K0456 • X13} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01235.proved (MV01236.proved))) (trans (cong refl Base.proved) (move-product MV01236.proved (MV01235.proved))))
