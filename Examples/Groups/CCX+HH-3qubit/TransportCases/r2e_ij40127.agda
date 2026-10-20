{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40127 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0127 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02111 as MV02111
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02112 as MV02112
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0127 ≈ K0127 • M4
proved = GL.•-cancelʳ {g = M4 • K0127} {g' = K0127 • M4} {h = p (s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02111.proved (MV02112.proved))) (trans (cong refl Base.proved) (move-product MV02112.proved (MV02111.proved))))
