{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij560137 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01719 as MV01719
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01720 as MV01720
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • K0137 ≈ K0137 • X56
proved = GL.•-cancelʳ {g = X56 • K0137} {g' = K0137 • X56} {h = p (s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01719.proved (MV01720.proved))) (trans (cong refl Base.proved) (move-product MV01720.proved (MV01719.proved))))
