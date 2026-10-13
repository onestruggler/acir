{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij570234 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01753 as MV01753
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01754 as MV01754
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X57 • K0234 ≈ K0234 • X57
proved = GL.•-cancelʳ {g = X57 • K0234} {g' = K0234 • X57} {h = p (s1 • s2 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01753.proved (MV01754.proved))) (trans (cong refl Base.proved) (move-product MV01754.proved (MV01753.proved))))
