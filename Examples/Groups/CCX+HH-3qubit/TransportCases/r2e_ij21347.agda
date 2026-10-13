{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij21347 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02016 as MV02016
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02017 as MV02017
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M2 • K1347 ≈ K1347 • M2
proved = GL.•-cancelʳ {g = M2 • K1347} {g' = K1347 • M2} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02016.proved (MV02017.proved))) (trans (cong refl Base.proved) (move-product MV02017.proved (MV02016.proved))))
