{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij560234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01723 as MV01723
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01724 as MV01724
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X56 • K0234 ≈ K0234 • X56
proved = GL.•-cancelʳ {g = X56 • K0234} {g' = K0234 • X56} {h = p (s1 • s2 • s3 • s4 • s5)}
  (trans (sym (move-product MV01723.proved (MV01724.proved))) (trans (cong refl Base.proved) (move-product MV01724.proved (MV01723.proved))))
