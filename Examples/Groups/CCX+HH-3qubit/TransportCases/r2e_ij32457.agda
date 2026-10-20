{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij32457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2457 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02099 as MV02099
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02100 as MV02100
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K2457 ≈ K2457 • M3
proved = GL.•-cancelʳ {g = M3 • K2457} {g' = K2457 • M3} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02099.proved (MV02100.proved))) (trans (cong refl Base.proved) (move-product MV02100.proved (MV02099.proved))))
