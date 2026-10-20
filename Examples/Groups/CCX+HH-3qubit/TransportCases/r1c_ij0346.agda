{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0346 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00666 as MV00666
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0346 • K0346 ≈ ε
proved = GL.•-cancelʳ {g = K0346 • K0346} {g' = ε} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00666.proved (MV00666.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
