{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0467 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00673 as MV00673
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0467 • K0467 ≈ ε
proved = GL.•-cancelʳ {g = K0467 • K0467} {g' = ε} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00673.proved (MV00673.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
