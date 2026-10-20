{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij60145 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0145 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02256 as MV02256
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02257 as MV02257
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M6 • K0145 ≈ K0145 • M6
proved = GL.•-cancelʳ {g = M6 • K0145} {g' = K0145 • M6} {h = p (s3 • s2 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02256.proved (MV02257.proved))) (trans (cong refl Base.proved) (move-product MV02257.proved (MV02256.proved))))
