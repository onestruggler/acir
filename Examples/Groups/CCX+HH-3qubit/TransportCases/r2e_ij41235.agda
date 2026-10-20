{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij41235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1235 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02145 as MV02145
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02146 as MV02146
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K1235 ≈ K1235 • M4
proved = GL.•-cancelʳ {g = M4 • K1235} {g' = K1235 • M4} {h = p (s0 • s1 • s2 • s4 • s3 • s4)}
  (trans (sym (move-product MV02145.proved (MV02146.proved))) (trans (cong refl Base.proved) (move-product MV02146.proved (MV02145.proved))))
