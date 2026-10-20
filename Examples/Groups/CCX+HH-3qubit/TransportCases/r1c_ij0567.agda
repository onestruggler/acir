{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0567 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00674 as MV00674
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0567 • K0567 ≈ ε
proved = GL.•-cancelʳ {g = K0567 • K0567} {g' = ε} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00674.proved (MV00674.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
