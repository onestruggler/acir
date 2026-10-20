{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij34567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K4567 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02105 as MV02105
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02106 as MV02106
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K4567 ≈ K4567 • M3
proved = GL.•-cancelʳ {g = M3 • K4567} {g' = K4567 • M3} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02105.proved (MV02106.proved))) (trans (cong refl Base.proved) (move-product MV02106.proved (MV02105.proved))))
