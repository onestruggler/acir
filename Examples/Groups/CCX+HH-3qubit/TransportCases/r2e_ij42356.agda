{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij42356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2356 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02165 as MV02165
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02166 as MV02166
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K2356 ≈ K2356 • M4
proved = GL.•-cancelʳ {g = M4 • K2356} {g' = K2356 • M4} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02165.proved (MV02166.proved))) (trans (cong refl Base.proved) (move-product MV02166.proved (MV02165.proved))))
