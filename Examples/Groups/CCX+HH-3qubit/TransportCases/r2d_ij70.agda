{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij70 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01887 as MV01887
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01888 as MV01888
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M7 • M0 ≈ M0 • M7
proved = GL.•-cancelʳ {g = M7 • M0} {g' = M0 • M7} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3)}
  (trans (sym (move-product MV01887.proved (MV01888.proved))) (trans (cong refl Base.proved) (move-product MV01888.proved (MV01887.proved))))
