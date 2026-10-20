{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02057 as MV02057
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02058 as MV02058
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K0245 ≈ K0245 • M3
proved = GL.•-cancelʳ {g = M3 • K0245} {g' = K0245 • M3} {h = p (s1 • s3 • s2 • s4 • s3 • s4)}
  (trans (sym (move-product MV02057.proved (MV02058.proved))) (trans (cong refl Base.proved) (move-product MV02058.proved (MV02057.proved))))
