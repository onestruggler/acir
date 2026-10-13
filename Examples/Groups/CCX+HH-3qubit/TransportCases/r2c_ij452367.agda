{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij452367 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01651 as MV01651
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01652 as MV01652
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K2367 ≈ K2367 • X45
proved = GL.•-cancelʳ {g = X45 • K2367} {g' = K2367 • X45} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01651.proved (MV01652.proved))) (trans (cong refl Base.proved) (move-product MV01652.proved (MV01651.proved))))
