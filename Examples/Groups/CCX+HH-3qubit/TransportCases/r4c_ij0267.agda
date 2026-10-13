{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0267 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00664 as MV00664
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02648 as MV02648
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02986 as MV02986
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • K0267 ≈ K0267 • X27
proved = GL.•-cancelʳ {g = X67 • K0267} {g' = K0267 • X27} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02986.proved (MV00664.proved))) (trans (cong refl Base.proved) (move-product MV00664.proved (MV02648.proved))))
