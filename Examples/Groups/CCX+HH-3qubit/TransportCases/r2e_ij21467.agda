{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij21467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1467 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02028 as MV02028
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02029 as MV02029
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K1467 ≈ K1467 • M2
proved = GL.•-cancelʳ {g = M2 • K1467} {g' = K1467 • M2} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02028.proved (MV02029.proved))) (trans (cong refl Base.proved) (move-product MV02029.proved (MV02028.proved))))
