{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij2567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2567 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00704 as MV00704
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K2567 • K2567 ≈ ε
proved = GL.•-cancelʳ {g = K2567 • K2567} {g' = ε} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00704.proved (MV00704.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
