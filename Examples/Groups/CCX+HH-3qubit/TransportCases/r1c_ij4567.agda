{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij4567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K4567 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00632 as MV00632
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K4567 • K4567 ≈ ε
proved = GL.•-cancelʳ {g = K4567 • K4567} {g' = ε} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00632.proved (MV00632.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
