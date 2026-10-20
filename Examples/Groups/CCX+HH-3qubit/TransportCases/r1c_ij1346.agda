{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij1346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1346 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00686 as MV00686
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K1346 • K1346 ≈ ε
proved = GL.•-cancelʳ {g = K1346 • K1346} {g' = ε} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00686.proved (MV00686.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
