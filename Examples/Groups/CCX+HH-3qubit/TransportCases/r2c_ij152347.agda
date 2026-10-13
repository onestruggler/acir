{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij152347 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01301 as MV01301
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01302 as MV01302
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X15 • K2347 ≈ K2347 • X15
proved = GL.•-cancelʳ {g = X15 • K2347} {g' = K2347 • X15} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01301.proved (MV01302.proved))) (trans (cong refl Base.proved) (move-product MV01302.proved (MV01301.proved))))
