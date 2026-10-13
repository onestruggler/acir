{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1347 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00687 as MV00687
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02740 as MV02740
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03009 as MV03009
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X47 • K1347 ≈ K1347 • X37
proved = GL.•-cancelʳ {g = X47 • K1347} {g' = K1347 • X37} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03009.proved (MV00687.proved))) (trans (cong refl Base.proved) (move-product MV00687.proved (MV02740.proved))))
