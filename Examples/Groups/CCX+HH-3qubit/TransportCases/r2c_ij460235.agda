{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij460235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01663 as MV01663
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01664 as MV01664
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X46 • K0235 ≈ K0235 • X46
proved = GL.•-cancelʳ {g = X46 • K0235} {g' = K0235 • X46} {h = p (s1 • s2 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01663.proved (MV01664.proved))) (trans (cong refl Base.proved) (move-product MV01664.proved (MV01663.proved))))
