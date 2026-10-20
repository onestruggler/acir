{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij250146 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0146 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01425 as MV01425
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01426 as MV01426
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X25 • K0146 ≈ K0146 • X25
proved = GL.•-cancelʳ {g = X25 • K0146} {g' = K0146 • X25} {h = p (s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01425.proved (MV01426.proved))) (trans (cong refl Base.proved) (move-product MV01426.proved (MV01425.proved))))
