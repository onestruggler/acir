{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij24560137 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; K2456 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00701 as MV00701
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02441 as MV02441
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K2456 • K0137 ≈ K0137 • K2456
proved = GL.•-cancelʳ {g = K2456 • K0137} {g' = K0137 • K2456} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00701.proved (MV02441.proved))) (trans (cong refl Base.proved) (move-product MV02441.proved (MV00701.proved))))
