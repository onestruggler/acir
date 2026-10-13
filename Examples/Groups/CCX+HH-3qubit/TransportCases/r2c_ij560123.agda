{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij560123 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01711 as MV01711
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01712 as MV01712
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • K0123 ≈ K0123 • X56
proved = GL.•-cancelʳ {g = X56 • K0123} {g' = K0123 • X56} {h = p (s4 • s5)}
  (trans (sym (move-product MV01711.proved (MV01712.proved))) (trans (cong refl Base.proved) (move-product MV01712.proved (MV01711.proved))))
