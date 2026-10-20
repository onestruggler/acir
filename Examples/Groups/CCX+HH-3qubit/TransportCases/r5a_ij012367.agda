{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij012367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0126 ; K1367 ; K2367 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01772 as MV01772
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03044 as MV03044
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03045 as MV03045
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03046 as MV03046
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K0123 • K1367 ≈ K2367 • K0126
proved = GL.•-cancelʳ {g = K0123 • K1367} {g' = K2367 • K0126} {h = p (s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01772.proved (MV03044.proved))) (trans (cong refl Base.proved) (move-product MV03045.proved (MV03046.proved))))
