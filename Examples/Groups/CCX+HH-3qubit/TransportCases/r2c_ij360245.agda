{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij360245 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01576 as MV01576
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01577 as MV01577
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X36 • K0245 ≈ K0245 • X36
proved = GL.•-cancelʳ {g = X36 • K0245} {g' = K0245 • X36} {h = p (s1 • s3 • s2 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01576.proved (MV01577.proved))) (trans (cong refl Base.proved) (move-product MV01577.proved (MV01576.proved))))
