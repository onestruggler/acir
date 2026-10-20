{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij51467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1467 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02231 as MV02231
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02232 as MV02232
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K1467 ≈ K1467 • M5
proved = GL.•-cancelʳ {g = M5 • K1467} {g' = K1467 • M5} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02231.proved (MV02232.proved))) (trans (cong refl Base.proved) (move-product MV02232.proved (MV02231.proved))))
