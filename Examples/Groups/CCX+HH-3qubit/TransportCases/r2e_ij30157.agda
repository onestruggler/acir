{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30157 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0157 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02053 as MV02053
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02054 as MV02054
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K0157 ≈ K0157 • M3
proved = GL.•-cancelʳ {g = M3 • K0157} {g' = K0157 • M3} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02053.proved (MV02054.proved))) (trans (cong refl Base.proved) (move-product MV02054.proved (MV02053.proved))))
