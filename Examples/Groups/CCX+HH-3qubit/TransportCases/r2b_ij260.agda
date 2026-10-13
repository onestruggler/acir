{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij260 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00890 as MV00890
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00891 as MV00891
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X26 • M0 ≈ M0 • X26
proved = GL.•-cancelʳ {g = X26 • M0} {g' = M0 • X26} {h = p (s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00890.proved (MV00891.proved))) (trans (cong refl Base.proved) (move-product MV00891.proved (MV00890.proved))))
