{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij250147 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01427 as MV01427
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01428 as MV01428
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X25 • K0147 ≈ K0147 • X25
proved = GL.•-cancelʳ {g = X25 • K0147} {g' = K0147 • X25} {h = p (s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01427.proved (MV01428.proved))) (trans (cong refl Base.proved) (move-product MV01428.proved (MV01427.proved))))
