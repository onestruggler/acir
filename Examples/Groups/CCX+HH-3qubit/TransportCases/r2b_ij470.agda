{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij470 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00986 as MV00986
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00987 as MV00987
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X47 • M0 ≈ M0 • X47
proved = GL.•-cancelʳ {g = X47 • M0} {g' = M0 • X47} {h = p (s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00986.proved (MV00987.proved))) (trans (cong refl Base.proved) (move-product MV00987.proved (MV00986.proved))))
