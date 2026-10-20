{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij02351467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0235 ; K1467 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00656 as MV00656
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02396 as MV02396
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0235 • K1467 ≈ K1467 • K0235
proved = GL.•-cancelʳ {g = K0235 • K1467} {g' = K1467 • K0235} {h = p (s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV00656.proved (MV02396.proved))) (trans (cong refl Base.proved) (move-product MV02396.proved (MV00656.proved))))
