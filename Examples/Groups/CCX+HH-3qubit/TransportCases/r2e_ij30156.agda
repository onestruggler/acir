{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30156 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0156 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02051 as MV02051
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02052 as MV02052
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K0156 ≈ K0156 • M3
proved = GL.•-cancelʳ {g = M3 • K0156} {g' = K0156 • M3} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02051.proved (MV02052.proved))) (trans (cong refl Base.proved) (move-product MV02052.proved (MV02051.proved))))
