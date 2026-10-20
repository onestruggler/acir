{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij562347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2347 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01739 as MV01739
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01740 as MV01740
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X56 • K2347 ≈ K2347 • X56
proved = GL.•-cancelʳ {g = X56 • K2347} {g' = K2347 • X56} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01739.proved (MV01740.proved))) (trans (cong refl Base.proved) (move-product MV01740.proved (MV01739.proved))))
