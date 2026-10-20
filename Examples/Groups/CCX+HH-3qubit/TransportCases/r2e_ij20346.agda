{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0346 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01994 as MV01994
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01995 as MV01995
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K0346 ≈ K0346 • M2
proved = GL.•-cancelʳ {g = M2 • K0346} {g' = K0346 • M2} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV01994.proved (MV01995.proved))) (trans (cong refl Base.proved) (move-product MV01995.proved (MV01994.proved))))
