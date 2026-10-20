{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij70245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02337 as MV02337
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02338 as MV02338
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K0245 ≈ K0245 • M7
proved = GL.•-cancelʳ {g = M7 • K0245} {g' = K0245 • M7} {h = p (s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02337.proved (MV02338.proved))) (trans (cong refl Base.proved) (move-product MV02338.proved (MV02337.proved))))
