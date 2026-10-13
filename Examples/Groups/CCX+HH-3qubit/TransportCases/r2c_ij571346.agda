{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij571346 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01767 as MV01767
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01768 as MV01768
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X57 • K1346 ≈ K1346 • X57
proved = GL.•-cancelʳ {g = X57 • K1346} {g' = K1346 • X57} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01767.proved (MV01768.proved))) (trans (cong refl Base.proved) (move-product MV01768.proved (MV01767.proved))))
