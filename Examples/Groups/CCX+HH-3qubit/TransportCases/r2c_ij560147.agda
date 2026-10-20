{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij560147 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0147 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01721 as MV01721
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01722 as MV01722
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X56 • K0147 ≈ K0147 • X56
proved = GL.•-cancelʳ {g = X56 • K0147} {g' = K0147 • X56} {h = p (s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01721.proved (MV01722.proved))) (trans (cong refl Base.proved) (move-product MV01722.proved (MV01721.proved))))
