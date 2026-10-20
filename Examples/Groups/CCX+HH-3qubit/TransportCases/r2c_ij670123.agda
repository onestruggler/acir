{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij670123 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01771 as MV01771
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01772 as MV01772
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X67 • K0123 ≈ K0123 • X67
proved = GL.•-cancelʳ {g = X67 • K0123} {g' = K0123 • X67} {h = p (s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01771.proved (MV01772.proved))) (trans (cong refl Base.proved) (move-product MV01772.proved (MV01771.proved))))
