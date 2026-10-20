{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij1245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1245 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00679 as MV00679
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K1245 • K1245 ≈ ε
proved = GL.•-cancelʳ {g = K1245 • K1245} {g' = ε} {h = p (s0 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV00679.proved (MV00679.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
