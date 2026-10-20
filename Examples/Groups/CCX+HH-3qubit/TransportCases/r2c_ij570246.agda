{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij570246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0246 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01757 as MV01757
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01758 as MV01758
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X57 • K0246 ≈ K0246 • X57
proved = GL.•-cancelʳ {g = X57 • K0246} {g' = K0246 • X57} {h = p (s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01757.proved (MV01758.proved))) (trans (cong refl Base.proved) (move-product MV01758.proved (MV01757.proved))))
