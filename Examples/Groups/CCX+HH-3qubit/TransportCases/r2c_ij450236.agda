{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij450236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0236 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01635 as MV01635
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01636 as MV01636
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X45 • K0236 ≈ K0236 • X45
proved = GL.•-cancelʳ {g = X45 • K0236} {g' = K0236 • X45} {h = p (s1 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01635.proved (MV01636.proved))) (trans (cong refl Base.proved) (move-product MV01636.proved (MV01635.proved))))
