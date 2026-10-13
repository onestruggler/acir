{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij170345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01351 as MV01351
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01352 as MV01352
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X17 • K0345 ≈ K0345 • X17
proved = GL.•-cancelʳ {g = X17 • K0345} {g' = K0345 • X17} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01351.proved (MV01352.proved))) (trans (cong refl Base.proved) (move-product MV01352.proved (MV01351.proved))))
