{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij170456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01357 as MV01357
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01358 as MV01358
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X17 • K0456 ≈ K0456 • X17
proved = GL.•-cancelʳ {g = X17 • K0456} {g' = K0456 • X17} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01357.proved (MV01358.proved))) (trans (cong refl Base.proved) (move-product MV01358.proved (MV01357.proved))))
