{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij470236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0236 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01695 as MV01695
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01696 as MV01696
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X47 • K0236 ≈ K0236 • X47
proved = GL.•-cancelʳ {g = X47 • K0236} {g' = K0236 • X47} {h = p (s1 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01695.proved (MV01696.proved))) (trans (cong refl Base.proved) (move-product MV01696.proved (MV01695.proved))))
