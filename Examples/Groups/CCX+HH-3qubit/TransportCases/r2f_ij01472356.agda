{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01472356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0147 ; K2356 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00651 as MV00651
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02391 as MV02391
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0147 • K2356 ≈ K2356 • K0147
proved = GL.•-cancelʳ {g = K0147 • K2356} {g' = K2356 • K0147} {h = p (s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00651.proved (MV02391.proved))) (trans (cong refl Base.proved) (move-product MV02391.proved (MV00651.proved))))
