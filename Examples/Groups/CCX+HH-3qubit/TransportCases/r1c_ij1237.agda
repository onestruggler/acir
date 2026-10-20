{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij1237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1237 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00678 as MV00678
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K1237 • K1237 ≈ ε
proved = GL.•-cancelʳ {g = K1237 • K1237} {g' = ε} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00678.proved (MV00678.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
