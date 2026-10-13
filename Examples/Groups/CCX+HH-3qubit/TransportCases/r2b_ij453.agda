{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij453 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00968 as MV00968
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00969 as MV00969
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • M3 ≈ M3 • X45
proved = GL.•-cancelʳ {g = X45 • M3} {g' = M3 • X45} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00968.proved (MV00969.proved))) (trans (cong refl Base.proved) (move-product MV00969.proved (MV00968.proved))))
