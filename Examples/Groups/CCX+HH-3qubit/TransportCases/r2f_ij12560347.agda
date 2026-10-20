{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij12560347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0347 ; K1256 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00682 as MV00682
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02422 as MV02422
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K1256 • K0347 ≈ K0347 • K1256
proved = GL.•-cancelʳ {g = K1256 • K0347} {g' = K0347 • K1256} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00682.proved (MV02422.proved))) (trans (cong refl Base.proved) (move-product MV02422.proved (MV00682.proved))))
