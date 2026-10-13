{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij570124 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01743 as MV01743
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01744 as MV01744
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X57 • K0124 ≈ K0124 • X57
proved = GL.•-cancelʳ {g = X57 • K0124} {g' = K0124 • X57} {h = p (s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01743.proved (MV01744.proved))) (trans (cong refl Base.proved) (move-product MV01744.proved (MV01743.proved))))
