{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0145 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0145 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s2 ; s3 ; s4 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00649 as MV00649
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0145 • K0145 ≈ ε
proved = GL.•-cancelʳ {g = K0145 • K0145} {g' = ε} {h = p (s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV00649.proved (MV00649.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
