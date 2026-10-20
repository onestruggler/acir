{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij250347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0347 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01433 as MV01433
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01434 as MV01434
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X25 • K0347 ≈ K0347 • X25
proved = GL.•-cancelʳ {g = X25 • K0347} {g' = K0347 • X25} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01433.proved (MV01434.proved))) (trans (cong refl Base.proved) (move-product MV01434.proved (MV01433.proved))))
