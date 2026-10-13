{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij360124 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01564 as MV01564
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01565 as MV01565
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X36 • K0124 ≈ K0124 • X36
proved = GL.•-cancelʳ {g = X36 • K0124} {g' = K0124 • X36} {h = p (s3 • s5)}
  (trans (sym (move-product MV01564.proved (MV01565.proved))) (trans (cong refl Base.proved) (move-product MV01565.proved (MV01564.proved))))
