{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30127 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0127 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00644 as MV00644
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02044 as MV02044
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K0127 ≈ K0127 • M3
proved = GL.•-cancelʳ {g = M3 • K0127} {g' = K0127 • M3} {h = p (s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02044.proved (MV00644.proved))) (trans (cong refl Base.proved) (move-product MV00644.proved (MV02044.proved))))
