{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0356 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00668 as MV00668
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0356 • K0356 ≈ ε
proved = GL.•-cancelʳ {g = K0356 • K0356} {g' = ε} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00668.proved (MV00668.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
