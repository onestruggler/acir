{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30145 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02045 as MV02045
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02046 as MV02046
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M3 • K0145 ≈ K0145 • M3
proved = GL.•-cancelʳ {g = M3 • K0145} {g' = K0145 • M3} {h = p (s3 • s2 • s4 • s3 • s4)}
  (trans (sym (move-product MV02045.proved (MV02046.proved))) (trans (cong refl Base.proved) (move-product MV02046.proved (MV02045.proved))))
