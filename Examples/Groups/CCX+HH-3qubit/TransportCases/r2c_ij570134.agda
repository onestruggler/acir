{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij570134 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01747 as MV01747
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01748 as MV01748
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X57 • K0134 ≈ K0134 • X57
proved = GL.•-cancelʳ {g = X57 • K0134} {g' = K0134 • X57} {h = p (s2 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01747.proved (MV01748.proved))) (trans (cong refl Base.proved) (move-product MV01748.proved (MV01747.proved))))
