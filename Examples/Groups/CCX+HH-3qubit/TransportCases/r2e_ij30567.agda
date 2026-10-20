{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0567 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02075 as MV02075
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02076 as MV02076
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K0567 ≈ K0567 • M3
proved = GL.•-cancelʳ {g = M3 • K0567} {g' = K0567 • M3} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02075.proved (MV02076.proved))) (trans (cong refl Base.proved) (move-product MV02076.proved (MV02075.proved))))
