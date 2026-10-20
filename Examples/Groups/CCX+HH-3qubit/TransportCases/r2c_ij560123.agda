{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij560123 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01711 as MV01711
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01712 as MV01712
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X56 • K0123 ≈ K0123 • X56
proved = GL.•-cancelʳ {g = X56 • K0123} {g' = K0123 • X56} {h = p (s4 • s5)}
  (trans (sym (move-product MV01711.proved (MV01712.proved))) (trans (cong refl Base.proved) (move-product MV01712.proved (MV01711.proved))))
