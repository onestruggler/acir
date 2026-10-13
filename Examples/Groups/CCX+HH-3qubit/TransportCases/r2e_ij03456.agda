{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij03456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00705 as MV00705
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01929 as MV01929
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M0 • K3456 ≈ K3456 • M0
proved = GL.•-cancelʳ {g = M0 • K3456} {g' = K3456 • M0} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01929.proved (MV00705.proved))) (trans (cong refl Base.proved) (move-product MV00705.proved (MV01929.proved))))
