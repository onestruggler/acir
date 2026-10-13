{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01992 as MV01992
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01993 as MV01993
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M2 • K0345 ≈ K0345 • M2
proved = GL.•-cancelʳ {g = M2 • K0345} {g' = K0345 • M2} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s4)}
  (trans (sym (move-product MV01992.proved (MV01993.proved))) (trans (cong refl Base.proved) (move-product MV01993.proved (MV01992.proved))))
