{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij140256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0256 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01256 as MV01256
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01257 as MV01257
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X14 • K0256 ≈ K0256 • X14
proved = GL.•-cancelʳ {g = X14 • K0256} {g' = K0256 • X14} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01256.proved (MV01257.proved))) (trans (cong refl Base.proved) (move-product MV01257.proved (MV01256.proved))))
