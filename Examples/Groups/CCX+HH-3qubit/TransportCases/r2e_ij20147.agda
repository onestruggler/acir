{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20147 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00651 as MV00651
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01988 as MV01988
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M2 • K0147 ≈ K0147 • M2
proved = GL.•-cancelʳ {g = M2 • K0147} {g' = K0147 • M2} {h = p (s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01988.proved (MV00651.proved))) (trans (cong refl Base.proved) (move-product MV00651.proved (MV01988.proved))))
