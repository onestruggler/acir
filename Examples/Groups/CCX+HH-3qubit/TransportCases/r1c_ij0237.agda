{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00658 as MV00658
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0237 • K0237 ≈ ε
proved = GL.•-cancelʳ {g = K0237 • K0237} {g' = ε} {h = p (s1 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00658.proved (MV00658.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
