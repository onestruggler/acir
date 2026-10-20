{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0457 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02071 as MV02071
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02072 as MV02072
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K0457 ≈ K0457 • M3
proved = GL.•-cancelʳ {g = M3 • K0457} {g' = K0457 • M3} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02071.proved (MV02072.proved))) (trans (cong refl Base.proved) (move-product MV02072.proved (MV02071.proved))))
