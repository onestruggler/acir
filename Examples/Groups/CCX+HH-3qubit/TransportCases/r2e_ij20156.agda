{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20156 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00652 as MV00652
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01989 as MV01989
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M2 • K0156 ≈ K0156 • M2
proved = GL.•-cancelʳ {g = M2 • K0156} {g' = K0156 • M2} {h = p (s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01989.proved (MV00652.proved))) (trans (cong refl Base.proved) (move-product MV00652.proved (MV01989.proved))))
