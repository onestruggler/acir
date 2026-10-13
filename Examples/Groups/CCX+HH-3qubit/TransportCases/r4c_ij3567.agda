{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij3567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00708 as MV00708
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02824 as MV02824
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03030 as MV03030
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • K3567 ≈ K3567 • X57
proved = GL.•-cancelʳ {g = X67 • K3567} {g' = K3567 • X57} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03030.proved (MV00708.proved))) (trans (cong refl Base.proved) (move-product MV00708.proved (MV02824.proved))))
