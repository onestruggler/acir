{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij34560127 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0127 ; K3456 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00705 as MV00705
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02445 as MV02445
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K3456 • K0127 ≈ K0127 • K3456
proved = GL.•-cancelʳ {g = K3456 • K0127} {g' = K0127 • K3456} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00705.proved (MV02445.proved))) (trans (cong refl Base.proved) (move-product MV02445.proved (MV00705.proved))))
