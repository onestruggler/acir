{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij560134 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01717 as MV01717
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01718 as MV01718
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • K0134 ≈ K0134 • X56
proved = GL.•-cancelʳ {g = X56 • K0134} {g' = K0134 • X56} {h = p (s2 • s3 • s4 • s5)}
  (trans (sym (move-product MV01717.proved (MV01718.proved))) (trans (cong refl Base.proved) (move-product MV01718.proved (MV01717.proved))))
