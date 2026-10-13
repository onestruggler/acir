{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij12 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01812 as MV01812
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01813 as MV01813
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M1 • M2 ≈ M2 • M1
proved = GL.•-cancelʳ {g = M1 • M2} {g' = M2 • M1} {h = p (s0 • s2 • s3)}
  (trans (sym (move-product MV01812.proved (MV01813.proved))) (trans (cong refl Base.proved) (move-product MV01813.proved (MV01812.proved))))
