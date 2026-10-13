{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij13456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01973 as MV01973
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01974 as MV01974
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M1 • K3456 ≈ K3456 • M1
proved = GL.•-cancelʳ {g = M1 • K3456} {g' = K3456 • M1} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV01973.proved (MV01974.proved))) (trans (cong refl Base.proved) (move-product MV01974.proved (MV01973.proved))))
