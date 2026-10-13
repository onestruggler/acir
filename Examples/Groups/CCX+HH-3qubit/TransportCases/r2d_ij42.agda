{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij42 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01852 as MV01852
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01853 as MV01853
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M4 • M2 ≈ M2 • M4
proved = GL.•-cancelʳ {g = M4 • M2} {g' = M2 • M4} {h = p (s3 • s2 • s1 • s0 • s3)}
  (trans (sym (move-product MV01852.proved (MV01853.proved))) (trans (cong refl Base.proved) (move-product MV01853.proved (MV01852.proved))))
