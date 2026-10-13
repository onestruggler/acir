{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij470235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01693 as MV01693
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01694 as MV01694
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X47 • K0235 ≈ K0235 • X47
proved = GL.•-cancelʳ {g = X47 • K0235} {g' = K0235 • X47} {h = p (s1 • s2 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01693.proved (MV01694.proved))) (trans (cong refl Base.proved) (move-product MV01694.proved (MV01693.proved))))
