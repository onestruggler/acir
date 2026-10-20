{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij263457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3457 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01477 as MV01477
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01478 as MV01478
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X26 • K3457 ≈ K3457 • X26
proved = GL.•-cancelʳ {g = X26 • K3457} {g' = K3457 • X26} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01477.proved (MV01478.proved))) (trans (cong refl Base.proved) (move-product MV01478.proved (MV01477.proved))))
