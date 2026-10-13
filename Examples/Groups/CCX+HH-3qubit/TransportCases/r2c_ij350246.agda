{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij350246 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01546 as MV01546
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01547 as MV01547
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • K0246 ≈ K0246 • X35
proved = GL.•-cancelʳ {g = X35 • K0246} {g' = K0246 • X35} {h = p (s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01546.proved (MV01547.proved))) (trans (cong refl Base.proved) (move-product MV01547.proved (MV01546.proved))))
