{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0125 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0125 ; X15 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00642 as MV00642
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02560 as MV02560
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02964 as MV02964
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X25 • K0125 ≈ K0125 • X15
proved = GL.•-cancelʳ {g = X25 • K0125} {g' = K0125 • X15} {h = p (s4 • s3)}
  (trans (sym (move-product MV02964.proved (MV00642.proved))) (trans (cong refl Base.proved) (move-product MV00642.proved (MV02560.proved))))
