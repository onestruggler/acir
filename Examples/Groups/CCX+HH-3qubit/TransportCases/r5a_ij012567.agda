{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij012567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01776 as MV01776
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03056 as MV03056
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03057 as MV03057
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03058 as MV03058
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0125 • K1567 ≈ K2567 • K0126
proved = GL.•-cancelʳ {g = K0125 • K1567} {g' = K2567 • K0126} {h = p (s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01776.proved (MV03056.proved))) (trans (cong refl Base.proved) (move-product MV03057.proved (MV03058.proved))))
