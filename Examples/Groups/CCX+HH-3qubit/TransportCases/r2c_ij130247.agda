{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij130247 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00661 as MV00661
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01231 as MV01231
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X13 • K0247 ≈ K0247 • X13
proved = GL.•-cancelʳ {g = X13 • K0247} {g' = K0247 • X13} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01231.proved (MV00661.proved))) (trans (cong refl Base.proved) (move-product MV00661.proved (MV01231.proved))))
