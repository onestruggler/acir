{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij460235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0235 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01663 as MV01663
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01664 as MV01664
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X46 • K0235 ≈ K0235 • X46
proved = GL.•-cancelʳ {g = X46 • K0235} {g' = K0235 • X46} {h = p (s1 • s2 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01663.proved (MV01664.proved))) (trans (cong refl Base.proved) (move-product MV01664.proved (MV01663.proved))))
