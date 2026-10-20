{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij2567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2567 ; X57 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00704 as MV00704
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02808 as MV02808
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03026 as MV03026
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X67 • K2567 ≈ K2567 • X57
proved = GL.•-cancelʳ {g = X67 • K2567} {g' = K2567 • X57} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03026.proved (MV00704.proved))) (trans (cong refl Base.proved) (move-product MV00704.proved (MV02808.proved))))
