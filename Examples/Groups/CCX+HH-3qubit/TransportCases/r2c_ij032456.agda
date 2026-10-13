{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij032456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01083 as MV01083
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01084 as MV01084
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X03 • K2456 ≈ K2456 • X03
proved = GL.•-cancelʳ {g = X03 • K2456} {g' = K2456 • X03} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01083.proved (MV01084.proved))) (trans (cong refl Base.proved) (move-product MV01084.proved (MV01083.proved))))
