{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij072356 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01203 as MV01203
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01204 as MV01204
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X07 • K2356 ≈ K2356 • X07
proved = GL.•-cancelʳ {g = X07 • K2356} {g' = K2356 • X07} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01203.proved (MV01204.proved))) (trans (cong refl Base.proved) (move-product MV01204.proved (MV01203.proved))))
