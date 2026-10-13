{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij240167 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01400 as MV01400
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01401 as MV01401
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • K0167 ≈ K0167 • X24
proved = GL.•-cancelʳ {g = X24 • K0167} {g' = K0167 • X24} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01400.proved (MV01401.proved))) (trans (cong refl Base.proved) (move-product MV01401.proved (MV01400.proved))))
