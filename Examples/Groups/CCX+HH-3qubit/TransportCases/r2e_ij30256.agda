{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0256 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02063 as MV02063
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02064 as MV02064
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K0256 ≈ K0256 • M3
proved = GL.•-cancelʳ {g = M3 • K0256} {g' = K0256 • M3} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02063.proved (MV02064.proved))) (trans (cong refl Base.proved) (move-product MV02064.proved (MV02063.proved))))
