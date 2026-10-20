{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij60237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02266 as MV02266
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02267 as MV02267
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M6 • K0237 ≈ K0237 • M6
proved = GL.•-cancelʳ {g = M6 • K0237} {g' = K0237 • M6} {h = p (s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02266.proved (MV02267.proved))) (trans (cong refl Base.proved) (move-product MV02267.proved (MV02266.proved))))
