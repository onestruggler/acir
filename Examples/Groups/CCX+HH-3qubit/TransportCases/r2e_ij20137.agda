{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20137 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00648 as MV00648
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01985 as MV01985
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K0137 ≈ K0137 • M2
proved = GL.•-cancelʳ {g = M2 • K0137} {g' = K0137 • M2} {h = p (s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01985.proved (MV00648.proved))) (trans (cong refl Base.proved) (move-product MV00648.proved (MV01985.proved))))
