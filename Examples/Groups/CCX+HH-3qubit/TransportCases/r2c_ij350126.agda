{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij350126 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01536 as MV01536
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01537 as MV01537
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • K0126 ≈ K0126 • X35
proved = GL.•-cancelʳ {g = X35 • K0126} {g' = K0126 • X35} {h = p (s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01536.proved (MV01537.proved))) (trans (cong refl Base.proved) (move-product MV01537.proved (MV01536.proved))))
