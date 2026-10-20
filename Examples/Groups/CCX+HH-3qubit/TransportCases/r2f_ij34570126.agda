{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij34570126 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0126 ; K3457 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00706 as MV00706
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02446 as MV02446
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K3457 • K0126 ≈ K0126 • K3457
proved = GL.•-cancelʳ {g = K3457 • K0126} {g' = K0126 • K3457} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00706.proved (MV02446.proved))) (trans (cong refl Base.proved) (move-product MV02446.proved (MV00706.proved))))
