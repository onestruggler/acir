{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0457 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02006 as MV02006
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02007 as MV02007
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K0457 ≈ K0457 • M2
proved = GL.•-cancelʳ {g = M2 • K0457} {g' = K0457 • M2} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02006.proved (MV02007.proved))) (trans (cong refl Base.proved) (move-product MV02007.proved (MV02006.proved))))
