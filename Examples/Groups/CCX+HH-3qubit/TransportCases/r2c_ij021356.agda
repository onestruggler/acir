{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij021356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1356 ; X02 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00688 as MV00688
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01052 as MV01052
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X02 • K1356 ≈ K1356 • X02
proved = GL.•-cancelʳ {g = X02 • K1356} {g' = K1356 • X02} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01052.proved (MV00688.proved))) (trans (cong refl Base.proved) (move-product MV00688.proved (MV01052.proved))))
