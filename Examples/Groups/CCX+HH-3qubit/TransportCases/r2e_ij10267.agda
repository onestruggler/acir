{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij10267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0267 ; M1 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00664 as MV00664
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01942 as MV01942
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M1 • K0267 ≈ K0267 • M1
proved = GL.•-cancelʳ {g = M1 • K0267} {g' = K0267 • M1} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01942.proved (MV00664.proved))) (trans (cong refl Base.proved) (move-product MV00664.proved (MV01942.proved))))
