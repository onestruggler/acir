{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij670135 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01779 as MV01779
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01780 as MV01780
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X67 • K0135 ≈ K0135 • X67
proved = GL.•-cancelʳ {g = X67 • K0135} {g' = K0135 • X67} {h = p (s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01779.proved (MV01780.proved))) (trans (cong refl Base.proved) (move-product MV01780.proved (MV01779.proved))))
