{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij470125 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0125 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01683 as MV01683
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01684 as MV01684
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X47 • K0125 ≈ K0125 • X47
proved = GL.•-cancelʳ {g = X47 • K0125} {g' = K0125 • X47} {h = p (s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01683.proved (MV01684.proved))) (trans (cong refl Base.proved) (move-product MV01684.proved (MV01683.proved))))
