{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij570126 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0126 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01745 as MV01745
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01746 as MV01746
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X57 • K0126 ≈ K0126 • X57
proved = GL.•-cancelʳ {g = X57 • K0126} {g' = K0126 • X57} {h = p (s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01745.proved (MV01746.proved))) (trans (cong refl Base.proved) (move-product MV01746.proved (MV01745.proved))))
