{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij670123 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01771 as MV01771
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01772 as MV01772
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • K0123 ≈ K0123 • X67
proved = GL.•-cancelʳ {g = X67 • K0123} {g' = K0123 • X67} {h = p (s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01771.proved (MV01772.proved))) (trans (cong refl Base.proved) (move-product MV01772.proved (MV01771.proved))))
