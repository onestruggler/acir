{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00672 as MV00672
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02680 as MV02680
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02994 as MV02994
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X57 • K0457 ≈ K0457 • X47
proved = GL.•-cancelʳ {g = X57 • K0457} {g' = K0457 • X47} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02994.proved (MV00672.proved))) (trans (cong refl Base.proved) (move-product MV00672.proved (MV02680.proved))))
