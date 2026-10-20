{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30145 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0145 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02045 as MV02045
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02046 as MV02046
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K0145 ≈ K0145 • M3
proved = GL.•-cancelʳ {g = M3 • K0145} {g' = K0145 • M3} {h = p (s3 • s2 • s4 • s3 • s4)}
  (trans (sym (move-product MV02045.proved (MV02046.proved))) (trans (cong refl Base.proved) (move-product MV02046.proved (MV02045.proved))))
