{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0367 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00670 as MV00670
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0367 • K0367 ≈ ε
proved = GL.•-cancelʳ {g = K0367 • K0367} {g' = ε} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00670.proved (MV00670.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
