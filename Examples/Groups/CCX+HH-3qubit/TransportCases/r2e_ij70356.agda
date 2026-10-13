{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij70356 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02347 as MV02347
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02348 as MV02348
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M7 • K0356 ≈ K0356 • M7
proved = GL.•-cancelʳ {g = M7 • K0356} {g' = K0356 • M7} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02347.proved (MV02348.proved))) (trans (cong refl Base.proved) (move-product MV02348.proved (MV02347.proved))))
