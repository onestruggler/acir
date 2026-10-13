{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij671235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01793 as MV01793
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01794 as MV01794
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • K1235 ≈ K1235 • X67
proved = GL.•-cancelʳ {g = X67 • K1235} {g' = K1235 • X67} {h = p (s0 • s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01793.proved (MV01794.proved))) (trans (cong refl Base.proved) (move-product MV01794.proved (MV01793.proved))))
