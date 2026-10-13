{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij570126 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01745 as MV01745
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01746 as MV01746
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X57 • K0126 ≈ K0126 • X57
proved = GL.•-cancelʳ {g = X57 • K0126} {g' = K0126 • X57} {h = p (s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01745.proved (MV01746.proved))) (trans (cong refl Base.proved) (move-product MV01746.proved (MV01745.proved))))
