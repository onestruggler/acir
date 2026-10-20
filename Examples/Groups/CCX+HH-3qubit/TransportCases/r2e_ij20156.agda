{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20156 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0156 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00652 as MV00652
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01989 as MV01989
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K0156 ≈ K0156 • M2
proved = GL.•-cancelʳ {g = M2 • K0156} {g' = K0156 • M2} {h = p (s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01989.proved (MV00652.proved))) (trans (cong refl Base.proved) (move-product MV00652.proved (MV01989.proved))))
