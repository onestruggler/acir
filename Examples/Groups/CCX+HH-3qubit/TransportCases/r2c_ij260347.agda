{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij260347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0347 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01463 as MV01463
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01464 as MV01464
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X26 • K0347 ≈ K0347 • X26
proved = GL.•-cancelʳ {g = X26 • K0347} {g' = K0347 • X26} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01463.proved (MV01464.proved))) (trans (cong refl Base.proved) (move-product MV01464.proved (MV01463.proved))))
