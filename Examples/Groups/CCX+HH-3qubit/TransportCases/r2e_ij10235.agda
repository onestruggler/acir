{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij10235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00656 as MV00656
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01934 as MV01934
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M1 • K0235 ≈ K0235 • M1
proved = GL.•-cancelʳ {g = M1 • K0235} {g' = K0235 • M1} {h = p (s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV01934.proved (MV00656.proved))) (trans (cong refl Base.proved) (move-product MV00656.proved (MV01934.proved))))
