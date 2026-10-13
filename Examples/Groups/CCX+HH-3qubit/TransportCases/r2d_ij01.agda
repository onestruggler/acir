{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij01 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01801 as MV01801
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01802 as MV01802
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M0 • M1 ≈ M1 • M0
proved = GL.•-cancelʳ {g = M0 • M1} {g' = M1 • M0} {h = p (s1 • s2 • s3)}
  (trans (sym (move-product MV01801.proved (MV01802.proved))) (trans (cong refl Base.proved) (move-product MV01802.proved (MV01801.proved))))
