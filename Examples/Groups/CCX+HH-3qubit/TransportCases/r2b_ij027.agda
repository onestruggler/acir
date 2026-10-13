{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij027 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00723 as MV00723
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00724 as MV00724
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X02 • M7 ≈ M7 • X02
proved = GL.•-cancelʳ {g = X02 • M7} {g' = M7 • X02} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2)}
  (trans (sym (move-product MV00723.proved (MV00724.proved))) (trans (cong refl Base.proved) (move-product MV00724.proved (MV00723.proved))))
