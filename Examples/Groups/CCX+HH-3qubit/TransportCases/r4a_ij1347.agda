{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1347 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00687 as MV00687
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02739 as MV02739
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02740 as MV02740
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02741 as MV02741
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02742 as MV02742
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X13 • K1347 ≈ K1347 • X37 • M3 • M7
proved = GL.•-cancelʳ {g = X13 • K1347} {g' = K1347 • X37 • M3 • M7} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02739.proved (MV00687.proved))) (trans (cong refl Base.proved) (move-product MV00687.proved (move-product MV02740.proved (move-product MV02741.proved (MV02742.proved))))))
