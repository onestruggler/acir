{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij470123 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01681 as MV01681
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01682 as MV01682
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X47 • K0123 ≈ K0123 • X47
proved = GL.•-cancelʳ {g = X47 • K0123} {g' = K0123 • X47} {h = p (s6 • s5)}
  (trans (sym (move-product MV01681.proved (MV01682.proved))) (trans (cong refl Base.proved) (move-product MV01682.proved (MV01681.proved))))
