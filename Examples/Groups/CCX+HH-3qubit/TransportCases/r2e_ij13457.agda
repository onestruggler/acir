{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij13457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01975 as MV01975
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01976 as MV01976
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M1 • K3457 ≈ K3457 • M1
proved = GL.•-cancelʳ {g = M1 • K3457} {g' = K3457 • M1} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV01975.proved (MV01976.proved))) (trans (cong refl Base.proved) (move-product MV01976.proved (MV01975.proved))))
