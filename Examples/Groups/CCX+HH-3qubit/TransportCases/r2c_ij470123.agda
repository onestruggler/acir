{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij470123 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01681 as MV01681
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01682 as MV01682
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X47 • K0123 ≈ K0123 • X47
proved = GL.•-cancelʳ {g = X47 • K0123} {g' = K0123 • X47} {h = p (s6 • s5)}
  (trans (sym (move-product MV01681.proved (MV01682.proved))) (trans (cong refl Base.proved) (move-product MV01682.proved (MV01681.proved))))
