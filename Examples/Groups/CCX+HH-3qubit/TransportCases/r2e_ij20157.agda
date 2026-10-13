{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20157 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00653 as MV00653
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01990 as MV01990
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M2 • K0157 ≈ K0157 • M2
proved = GL.•-cancelʳ {g = M2 • K0157} {g' = K0157 • M2} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01990.proved (MV00653.proved))) (trans (cong refl Base.proved) (move-product MV00653.proved (MV01990.proved))))
