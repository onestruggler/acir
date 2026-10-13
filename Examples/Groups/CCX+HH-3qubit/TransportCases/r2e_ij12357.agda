{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij12357 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01961 as MV01961
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01962 as MV01962
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M1 • K2357 ≈ K2357 • M1
proved = GL.•-cancelʳ {g = M1 • K2357} {g' = K2357 • M1} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV01961.proved (MV01962.proved))) (trans (cong refl Base.proved) (move-product MV01962.proved (MV01961.proved))))
