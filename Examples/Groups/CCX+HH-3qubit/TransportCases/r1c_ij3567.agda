{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij3567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3567 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00708 as MV00708
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K3567 • K3567 ≈ ε
proved = GL.•-cancelʳ {g = K3567 • K3567} {g' = ε} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00708.proved (MV00708.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
