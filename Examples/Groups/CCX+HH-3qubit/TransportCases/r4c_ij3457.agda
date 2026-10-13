{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij3457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00706 as MV00706
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02816 as MV02816
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03028 as MV03028
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X57 • K3457 ≈ K3457 • X47
proved = GL.•-cancelʳ {g = X57 • K3457} {g' = K3457 • X47} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03028.proved (MV00706.proved))) (trans (cong refl Base.proved) (move-product MV00706.proved (MV02816.proved))))
