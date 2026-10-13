{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50137 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02185 as MV02185
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02186 as MV02186
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M5 • K0137 ≈ K0137 • M5
proved = GL.•-cancelʳ {g = M5 • K0137} {g' = K0137 • M5} {h = p (s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02185.proved (MV02186.proved))) (trans (cong refl Base.proved) (move-product MV02186.proved (MV02185.proved))))
