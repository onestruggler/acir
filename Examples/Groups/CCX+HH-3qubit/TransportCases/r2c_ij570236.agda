{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij570236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0236 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01755 as MV01755
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01756 as MV01756
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X57 • K0236 ≈ K0236 • X57
proved = GL.•-cancelʳ {g = X57 • K0236} {g' = K0236 • X57} {h = p (s1 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01755.proved (MV01756.proved))) (trans (cong refl Base.proved) (move-product MV01756.proved (MV01755.proved))))
