{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij561247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1247 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01735 as MV01735
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01736 as MV01736
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X56 • K1247 ≈ K1247 • X56
proved = GL.•-cancelʳ {g = X56 • K1247} {g' = K1247 • X56} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01735.proved (MV01736.proved))) (trans (cong refl Base.proved) (move-product MV01736.proved (MV01735.proved))))
