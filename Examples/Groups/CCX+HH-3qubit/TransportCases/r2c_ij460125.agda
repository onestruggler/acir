{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij460125 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0125 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01653 as MV01653
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01654 as MV01654
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X46 • K0125 ≈ K0125 • X46
proved = GL.•-cancelʳ {g = X46 • K0125} {g' = K0125 • X46} {h = p (s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01653.proved (MV01654.proved))) (trans (cong refl Base.proved) (move-product MV01654.proved (MV01653.proved))))
