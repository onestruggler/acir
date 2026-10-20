{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij270356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0356 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01495 as MV01495
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01496 as MV01496
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X27 • K0356 ≈ K0356 • X27
proved = GL.•-cancelʳ {g = X27 • K0356} {g' = K0356 • X27} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01495.proved (MV01496.proved))) (trans (cong refl Base.proved) (move-product MV01496.proved (MV01495.proved))))
