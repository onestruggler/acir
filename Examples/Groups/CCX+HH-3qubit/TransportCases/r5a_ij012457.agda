{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij012457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01744 as MV01744
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03050 as MV03050
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03051 as MV03051
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03052 as MV03052
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0124 • K1457 ≈ K2457 • K0125
proved = GL.•-cancelʳ {g = K0124 • K1457} {g' = K2457 • K0125} {h = p (s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01744.proved (MV03050.proved))) (trans (cong refl Base.proved) (move-product MV03051.proved (MV03052.proved))))
