{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij260345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0345 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01461 as MV01461
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01462 as MV01462
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X26 • K0345 ≈ K0345 • X26
proved = GL.•-cancelʳ {g = X26 • K0345} {g' = K0345 • X26} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01461.proved (MV01462.proved))) (trans (cong refl Base.proved) (move-product MV01462.proved (MV01461.proved))))
