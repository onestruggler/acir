{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij23460157 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0157 ; K2346 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00696 as MV00696
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02436 as MV02436
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K2346 • K0157 ≈ K0157 • K2346
proved = GL.•-cancelʳ {g = K2346 • K0157} {g' = K0157 • K2346} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00696.proved (MV02436.proved))) (trans (cong refl Base.proved) (move-product MV02436.proved (MV00696.proved))))
