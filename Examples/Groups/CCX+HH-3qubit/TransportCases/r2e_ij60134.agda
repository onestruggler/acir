{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij60134 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02250 as MV02250
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02251 as MV02251
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M6 • K0134 ≈ K0134 • M6
proved = GL.•-cancelʳ {g = M6 • K0134} {g' = K0134 • M6} {h = p (s2 • s3 • s5 • s4)}
  (trans (sym (move-product MV02250.proved (MV02251.proved))) (trans (cong refl Base.proved) (move-product MV02251.proved (MV02250.proved))))
