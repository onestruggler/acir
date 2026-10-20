{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0235 ; X25 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00656 as MV00656
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02616 as MV02616
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02978 as MV02978
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X35 • K0235 ≈ K0235 • X25
proved = GL.•-cancelʳ {g = X35 • K0235} {g' = K0235 • X25} {h = p (s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV02978.proved (MV00656.proved))) (trans (cong refl Base.proved) (move-product MV00656.proved (MV02616.proved))))
