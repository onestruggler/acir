{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij570346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0346 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01759 as MV01759
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01760 as MV01760
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X57 • K0346 ≈ K0346 • X57
proved = GL.•-cancelʳ {g = X57 • K0346} {g' = K0346 • X57} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01759.proved (MV01760.proved))) (trans (cong refl Base.proved) (move-product MV01760.proved (MV01759.proved))))
