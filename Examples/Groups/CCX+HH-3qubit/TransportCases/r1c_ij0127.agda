{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0127 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0127 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00644 as MV00644
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0127 • K0127 ≈ ε
proved = GL.•-cancelʳ {g = K0127 • K0127} {g' = ε} {h = p (s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00644.proved (MV00644.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
