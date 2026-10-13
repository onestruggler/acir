{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij150267 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01289 as MV01289
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01290 as MV01290
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X15 • K0267 ≈ K0267 • X15
proved = GL.•-cancelʳ {g = X15 • K0267} {g' = K0267 • X15} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01289.proved (MV01290.proved))) (trans (cong refl Base.proved) (move-product MV01290.proved (MV01289.proved))))
