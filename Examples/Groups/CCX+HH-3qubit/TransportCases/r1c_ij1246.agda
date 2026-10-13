{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij1246 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00680 as MV00680
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K1246 • K1246 ≈ ε
proved = GL.•-cancelʳ {g = K1246 • K1246} {g' = ε} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00680.proved (MV00680.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
