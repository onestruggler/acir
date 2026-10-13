{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0347 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00667 as MV00667
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02660 as MV02660
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02989 as MV02989
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X47 • K0347 ≈ K0347 • X37
proved = GL.•-cancelʳ {g = X47 • K0347} {g' = K0347 • X37} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02989.proved (MV00667.proved))) (trans (cong refl Base.proved) (move-product MV00667.proved (MV02660.proved))))
