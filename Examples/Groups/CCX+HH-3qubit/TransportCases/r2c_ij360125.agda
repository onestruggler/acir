{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij360125 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01566 as MV01566
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01567 as MV01567
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X36 • K0125 ≈ K0125 • X36
proved = GL.•-cancelʳ {g = X36 • K0125} {g' = K0125 • X36} {h = p (s4 • s3 • s5)}
  (trans (sym (move-product MV01566.proved (MV01567.proved))) (trans (cong refl Base.proved) (move-product MV01567.proved (MV01566.proved))))
