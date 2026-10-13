{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0257 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00663 as MV00663
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02871 as MV02871
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02872 as MV02872
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X25 • K0257 ≈ M0 • K0257 • M0 • K0257 • M0
proved = GL.•-cancelʳ {g = X25 • K0257} {g' = M0 • K0257 • M0 • K0257 • M0} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02871.proved (MV00663.proved))) (trans (cong refl Base.proved) (move-product MV02872.proved (move-product MV00663.proved (move-product MV02872.proved (move-product MV00663.proved (MV02872.proved)))))))
