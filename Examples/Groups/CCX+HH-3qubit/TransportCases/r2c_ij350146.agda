{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij350146 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01540 as MV01540
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01541 as MV01541
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • K0146 ≈ K0146 • X35
proved = GL.•-cancelʳ {g = X35 • K0146} {g' = K0146 • X35} {h = p (s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01540.proved (MV01541.proved))) (trans (cong refl Base.proved) (move-product MV01541.proved (MV01540.proved))))
