{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij60 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01874 as MV01874
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01875 as MV01875
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M6 • M0 ≈ M0 • M6
proved = GL.•-cancelʳ {g = M6 • M0} {g' = M0 • M6} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3)}
  (trans (sym (move-product MV01874.proved (MV01875.proved))) (trans (cong refl Base.proved) (move-product MV01875.proved (MV01874.proved))))
