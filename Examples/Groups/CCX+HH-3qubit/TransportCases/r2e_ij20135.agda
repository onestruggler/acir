{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20135 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00646 as MV00646
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01983 as MV01983
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K0135 ≈ K0135 • M2
proved = GL.•-cancelʳ {g = M2 • K0135} {g' = K0135 • M2} {h = p (s2 • s4 • s3)}
  (trans (sym (move-product MV01983.proved (MV00646.proved))) (trans (cong refl Base.proved) (move-product MV00646.proved (MV01983.proved))))
