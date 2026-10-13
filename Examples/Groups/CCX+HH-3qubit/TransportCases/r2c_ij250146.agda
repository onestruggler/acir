{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij250146 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01425 as MV01425
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01426 as MV01426
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X25 • K0146 ≈ K0146 • X25
proved = GL.•-cancelʳ {g = X25 • K0146} {g' = K0146 • X25} {h = p (s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01425.proved (MV01426.proved))) (trans (cong refl Base.proved) (move-product MV01426.proved (MV01425.proved))))
