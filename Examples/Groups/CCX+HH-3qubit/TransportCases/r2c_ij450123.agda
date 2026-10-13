{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij450123 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00641 as MV00641
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01624 as MV01624
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K0123 ≈ K0123 • X45
proved = GL.•-cancelʳ {g = X45 • K0123} {g' = K0123 • X45} {h = p (ε)}
  (trans (sym (move-product MV01624.proved (MV00641.proved))) (trans (cong refl Base.proved) (move-product MV00641.proved (MV01624.proved))))
