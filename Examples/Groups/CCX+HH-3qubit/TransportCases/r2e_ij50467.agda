{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02211 as MV02211
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02212 as MV02212
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M5 • K0467 ≈ K0467 • M5
proved = GL.•-cancelʳ {g = M5 • K0467} {g' = K0467 • M5} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02211.proved (MV02212.proved))) (trans (cong refl Base.proved) (move-product MV02212.proved (MV02211.proved))))
