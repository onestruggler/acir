{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij062347 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01171 as MV01171
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01172 as MV01172
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X06 • K2347 ≈ K2347 • X06
proved = GL.•-cancelʳ {g = X06 • K2347} {g' = K2347 • X06} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01171.proved (MV01172.proved))) (trans (cong refl Base.proved) (move-product MV01172.proved (MV01171.proved))))
