{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij270456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0456 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01497 as MV01497
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01498 as MV01498
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X27 • K0456 ≈ K0456 • X27
proved = GL.•-cancelʳ {g = X27 • K0456} {g' = K0456 • X27} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01497.proved (MV01498.proved))) (trans (cong refl Base.proved) (move-product MV01498.proved (MV01497.proved))))
