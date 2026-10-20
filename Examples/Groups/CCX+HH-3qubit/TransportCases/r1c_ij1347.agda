{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij1347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1347 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00687 as MV00687
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K1347 • K1347 ≈ ε
proved = GL.•-cancelʳ {g = K1347 • K1347} {g' = ε} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00687.proved (MV00687.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
