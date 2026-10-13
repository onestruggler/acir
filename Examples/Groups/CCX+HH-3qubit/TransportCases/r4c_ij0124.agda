{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0124 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00113 as MV00113
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00147 as MV00147
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as MV00245
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • K0124 ≈ K0124 • X14
proved = GL.•-cancelʳ {g = X24 • K0124} {g' = K0124 • X14} {h = p (s3)}
  (trans (sym (move-product MV00147.proved (MV00245.proved))) (trans (cong refl Base.proved) (move-product MV00245.proved (MV00113.proved))))
