{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij350127 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01538 as MV01538
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01539 as MV01539
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • K0127 ≈ K0127 • X35
proved = GL.•-cancelʳ {g = X35 • K0127} {g' = K0127 • X35} {h = p (s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01538.proved (MV01539.proved))) (trans (cong refl Base.proved) (move-product MV01539.proved (MV01538.proved))))
