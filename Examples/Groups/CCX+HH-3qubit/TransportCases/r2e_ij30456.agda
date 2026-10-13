{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02069 as MV02069
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02070 as MV02070
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M3 • K0456 ≈ K0456 • M3
proved = GL.•-cancelʳ {g = M3 • K0456} {g' = K0456 • M3} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02069.proved (MV02070.proved))) (trans (cong refl Base.proved) (move-product MV02070.proved (MV02069.proved))))
