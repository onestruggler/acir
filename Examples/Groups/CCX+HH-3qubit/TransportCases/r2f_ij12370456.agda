{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij12370456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0456 ; K1237 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00678 as MV00678
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02418 as MV02418
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K1237 • K0456 ≈ K0456 • K1237
proved = GL.•-cancelʳ {g = K1237 • K0456} {g' = K0456 • K1237} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00678.proved (MV02418.proved))) (trans (cong refl Base.proved) (move-product MV02418.proved (MV00678.proved))))
