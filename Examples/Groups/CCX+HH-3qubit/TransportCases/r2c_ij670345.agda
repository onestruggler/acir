{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij670345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0345 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01789 as MV01789
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01790 as MV01790
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X67 • K0345 ≈ K0345 • X67
proved = GL.•-cancelʳ {g = X67 • K0345} {g' = K0345 • X67} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01789.proved (MV01790.proved))) (trans (cong refl Base.proved) (move-product MV01790.proved (MV01789.proved))))
