{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0457 ; X47 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00672 as MV00672
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02680 as MV02680
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02994 as MV02994
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X57 • K0457 ≈ K0457 • X47
proved = GL.•-cancelʳ {g = X57 • K0457} {g' = K0457 • X47} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02994.proved (MV00672.proved))) (trans (cong refl Base.proved) (move-product MV00672.proved (MV02680.proved))))
