{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0127 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0127 ; X17 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00644 as MV00644
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02568 as MV02568
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02966 as MV02966
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X27 • K0127 ≈ K0127 • X17
proved = GL.•-cancelʳ {g = X27 • K0127} {g' = K0127 • X17} {h = p (s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02966.proved (MV00644.proved))) (trans (cong refl Base.proved) (move-product MV00644.proved (MV02568.proved))))
