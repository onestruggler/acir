{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij170346 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01353 as MV01353
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01354 as MV01354
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X17 • K0346 ≈ K0346 • X17
proved = GL.•-cancelʳ {g = X17 • K0346} {g' = K0346 • X17} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01353.proved (MV01354.proved))) (trans (cong refl Base.proved) (move-product MV01354.proved (MV01353.proved))))
