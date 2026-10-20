{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0267 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02135 as MV02135
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02136 as MV02136
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0267 ≈ K0267 • M4
proved = GL.•-cancelʳ {g = M4 • K0267} {g' = K0267 • M4} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02135.proved (MV02136.proved))) (trans (cong refl Base.proved) (move-product MV02136.proved (MV02135.proved))))
