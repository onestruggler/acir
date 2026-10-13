{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij670124 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01773 as MV01773
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01774 as MV01774
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • K0124 ≈ K0124 • X67
proved = GL.•-cancelʳ {g = X67 • K0124} {g' = K0124 • X67} {h = p (s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01773.proved (MV01774.proved))) (trans (cong refl Base.proved) (move-product MV01774.proved (MV01773.proved))))
