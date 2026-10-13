{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij10256 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00662 as MV00662
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01940 as MV01940
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M1 • K0256 ≈ K0256 • M1
proved = GL.•-cancelʳ {g = M1 • K0256} {g' = K0256 • M1} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01940.proved (MV00662.proved))) (trans (cong refl Base.proved) (move-product MV00662.proved (MV01940.proved))))
