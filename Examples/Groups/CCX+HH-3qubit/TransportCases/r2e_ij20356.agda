{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0356 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01998 as MV01998
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01999 as MV01999
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K0356 ≈ K0356 • M2
proved = GL.•-cancelʳ {g = M2 • K0356} {g' = K0356 • M2} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV01998.proved (MV01999.proved))) (trans (cong refl Base.proved) (move-product MV01999.proved (MV01998.proved))))
