{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij10245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; M1 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00659 as MV00659
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01937 as MV01937
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M1 • K0245 ≈ K0245 • M1
proved = GL.•-cancelʳ {g = M1 • K0245} {g' = K0245 • M1} {h = p (s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV01937.proved (MV00659.proved))) (trans (cong refl Base.proved) (move-product MV00659.proved (MV01937.proved))))
