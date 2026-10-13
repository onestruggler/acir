{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40127 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02111 as MV02111
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02112 as MV02112
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M4 • K0127 ≈ K0127 • M4
proved = GL.•-cancelʳ {g = M4 • K0127} {g' = K0127 • M4} {h = p (s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02111.proved (MV02112.proved))) (trans (cong refl Base.proved) (move-product MV02112.proved (MV02111.proved))))
