{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij260134 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01449 as MV01449
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01450 as MV01450
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X26 • K0134 ≈ K0134 • X26
proved = GL.•-cancelʳ {g = X26 • K0134} {g' = K0134 • X26} {h = p (s2 • s3 • s5)}
  (trans (sym (move-product MV01449.proved (MV01450.proved))) (trans (cong refl Base.proved) (move-product MV01450.proved (MV01449.proved))))
