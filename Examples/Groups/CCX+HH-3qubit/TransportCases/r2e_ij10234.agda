{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij10234 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00655 as MV00655
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01802 as MV01802
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M1 • K0234 ≈ K0234 • M1
proved = GL.•-cancelʳ {g = M1 • K0234} {g' = K0234 • M1} {h = p (s1 • s2 • s3)}
  (trans (sym (move-product MV01802.proved (MV00655.proved))) (trans (cong refl Base.proved) (move-product MV00655.proved (MV01802.proved))))
