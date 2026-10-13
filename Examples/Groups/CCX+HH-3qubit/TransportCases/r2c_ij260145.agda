{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij260145 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01455 as MV01455
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01456 as MV01456
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X26 • K0145 ≈ K0145 • X26
proved = GL.•-cancelʳ {g = X26 • K0145} {g' = K0145 • X26} {h = p (s3 • s2 • s4 • s3 • s5)}
  (trans (sym (move-product MV01455.proved (MV01456.proved))) (trans (cong refl Base.proved) (move-product MV01456.proved (MV01455.proved))))
