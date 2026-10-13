{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij041235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00676 as MV00676
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01093 as MV01093
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X04 • K1235 ≈ K1235 • X04
proved = GL.•-cancelʳ {g = X04 • K1235} {g' = K1235 • X04} {h = p (s0 • s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV01093.proved (MV00676.proved))) (trans (cong refl Base.proved) (move-product MV00676.proved (MV01093.proved))))
