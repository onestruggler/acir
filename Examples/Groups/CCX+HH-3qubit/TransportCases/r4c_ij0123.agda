{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0123 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00641 as MV00641
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02556 as MV02556
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02963 as MV02963
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X23 • K0123 ≈ K0123 • X13
proved = GL.•-cancelʳ {g = X23 • K0123} {g' = K0123 • X13} {h = p (ε)}
  (trans (sym (move-product MV02963.proved (MV00641.proved))) (trans (cong refl Base.proved) (move-product MV00641.proved (MV02556.proved))))
