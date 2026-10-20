{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij60457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0457 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02280 as MV02280
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02281 as MV02281
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M6 • K0457 ≈ K0457 • M6
proved = GL.•-cancelʳ {g = M6 • K0457} {g' = K0457 • M6} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02280.proved (MV02281.proved))) (trans (cong refl Base.proved) (move-product MV02281.proved (MV02280.proved))))
