{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40125 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02107 as MV02107
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02108 as MV02108
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M4 • K0125 ≈ K0125 • M4
proved = GL.•-cancelʳ {g = M4 • K0125} {g' = K0125 • M4} {h = p (s4 • s3 • s4)}
  (trans (sym (move-product MV02107.proved (MV02108.proved))) (trans (cong refl Base.proved) (move-product MV02108.proved (MV02107.proved))))
