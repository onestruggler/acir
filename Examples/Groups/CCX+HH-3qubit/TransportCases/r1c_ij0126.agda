{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0126 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0126 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s3 ; s4 ; s5 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00643 as MV00643
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0126 • K0126 ≈ ε
proved = GL.•-cancelʳ {g = K0126 • K0126} {g' = ε} {h = p (s5 • s4 • s3)}
  (trans (sym (move-product MV00643.proved (MV00643.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
