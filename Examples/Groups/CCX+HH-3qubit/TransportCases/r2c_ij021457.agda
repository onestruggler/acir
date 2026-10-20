{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij021457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1457 ; X02 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00692 as MV00692
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01056 as MV01056
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X02 • K1457 ≈ K1457 • X02
proved = GL.•-cancelʳ {g = X02 • K1457} {g' = K1457 • X02} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01056.proved (MV00692.proved))) (trans (cong refl Base.proved) (move-product MV00692.proved (MV01056.proved))))
