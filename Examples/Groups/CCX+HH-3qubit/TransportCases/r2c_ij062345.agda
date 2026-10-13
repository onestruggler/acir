{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij062345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01169 as MV01169
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01170 as MV01170
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X06 • K2345 ≈ K2345 • X06
proved = GL.•-cancelʳ {g = X06 • K2345} {g' = K2345 • X06} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5)}
  (trans (sym (move-product MV01169.proved (MV01170.proved))) (trans (cong refl Base.proved) (move-product MV01170.proved (MV01169.proved))))
