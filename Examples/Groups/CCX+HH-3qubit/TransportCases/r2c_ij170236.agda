{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij170236 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01343 as MV01343
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01344 as MV01344
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X17 • K0236 ≈ K0236 • X17
proved = GL.•-cancelʳ {g = X17 • K0236} {g' = K0236 • X17} {h = p (s1 • s2 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01343.proved (MV01344.proved))) (trans (cong refl Base.proved) (move-product MV01344.proved (MV01343.proved))))
