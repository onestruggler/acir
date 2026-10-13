{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1257 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00683 as MV00683
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02724 as MV02724
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03005 as MV03005
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X57 • K1257 ≈ K1257 • X27
proved = GL.•-cancelʳ {g = X57 • K1257} {g' = K1257 • X27} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03005.proved (MV00683.proved))) (trans (cong refl Base.proved) (move-product MV00683.proved (MV02724.proved))))
