{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij130267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0267 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00664 as MV00664
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01234 as MV01234
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X13 • K0267 ≈ K0267 • X13
proved = GL.•-cancelʳ {g = X13 • K0267} {g' = K0267 • X13} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01234.proved (MV00664.proved))) (trans (cong refl Base.proved) (move-product MV00664.proved (MV01234.proved))))
