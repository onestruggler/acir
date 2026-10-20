{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij570234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01753 as MV01753
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01754 as MV01754
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X57 • K0234 ≈ K0234 • X57
proved = GL.•-cancelʳ {g = X57 • K0234} {g' = K0234 • X57} {h = p (s1 • s2 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01753.proved (MV01754.proved))) (trans (cong refl Base.proved) (move-product MV01754.proved (MV01753.proved))))
