{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij270156 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01489 as MV01489
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01490 as MV01490
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X27 • K0156 ≈ K0156 • X27
proved = GL.•-cancelʳ {g = X27 • K0156} {g' = K0156 • X27} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01489.proved (MV01490.proved))) (trans (cong refl Base.proved) (move-product MV01490.proved (MV01489.proved))))
