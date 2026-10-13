{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij470135 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01687 as MV01687
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01688 as MV01688
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X47 • K0135 ≈ K0135 • X47
proved = GL.•-cancelʳ {g = X47 • K0135} {g' = K0135 • X47} {h = p (s2 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01687.proved (MV01688.proved))) (trans (cong refl Base.proved) (move-product MV01688.proved (MV01687.proved))))
