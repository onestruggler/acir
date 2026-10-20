{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij470135 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01687 as MV01687
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01688 as MV01688
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X47 • K0135 ≈ K0135 • X47
proved = GL.•-cancelʳ {g = X47 • K0135} {g' = K0135 • X47} {h = p (s2 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01687.proved (MV01688.proved))) (trans (cong refl Base.proved) (move-product MV01688.proved (MV01687.proved))))
