{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij450123 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00641 as MV00641
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01624 as MV01624
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X45 • K0123 ≈ K0123 • X45
proved = GL.•-cancelʳ {g = X45 • K0123} {g' = K0123 • X45} {h = p (ε)}
  (trans (sym (move-product MV01624.proved (MV00641.proved))) (trans (cong refl Base.proved) (move-product MV00641.proved (MV01624.proved))))
