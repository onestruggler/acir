{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30146 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0146 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02047 as MV02047
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02048 as MV02048
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K0146 ≈ K0146 • M3
proved = GL.•-cancelʳ {g = M3 • K0146} {g' = K0146 • M3} {h = p (s3 • s2 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02047.proved (MV02048.proved))) (trans (cong refl Base.proved) (move-product MV02048.proved (MV02047.proved))))
