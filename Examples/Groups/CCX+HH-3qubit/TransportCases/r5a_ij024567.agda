{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij024567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01788 as MV01788
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03086 as MV03086
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03087 as MV03087
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03088 as MV03088
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0245 • K2567 ≈ K4567 • K0246
proved = GL.•-cancelʳ {g = K0245 • K2567} {g' = K4567 • K0246} {h = p (s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01788.proved (MV03086.proved))) (trans (cong refl Base.proved) (move-product MV03087.proved (MV03088.proved))))
