{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij470356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0356 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01699 as MV01699
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01700 as MV01700
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X47 • K0356 ≈ K0356 • X47
proved = GL.•-cancelʳ {g = X47 • K0356} {g' = K0356 • X47} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01699.proved (MV01700.proved))) (trans (cong refl Base.proved) (move-product MV01700.proved (MV01699.proved))))
