{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij70456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0456 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02349 as MV02349
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02350 as MV02350
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K0456 ≈ K0456 • M7
proved = GL.•-cancelʳ {g = M7 • K0456} {g' = K0456 • M7} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02349.proved (MV02350.proved))) (trans (cong refl Base.proved) (move-product MV02350.proved (MV02349.proved))))
