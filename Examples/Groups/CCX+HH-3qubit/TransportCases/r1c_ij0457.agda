{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0457 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00672 as MV00672
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0457 • K0457 ≈ ε
proved = GL.•-cancelʳ {g = K0457 • K0457} {g' = ε} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00672.proved (MV00672.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
