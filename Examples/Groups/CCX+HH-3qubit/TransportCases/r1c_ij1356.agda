{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij1356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1356 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00688 as MV00688
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K1356 • K1356 ≈ ε
proved = GL.•-cancelʳ {g = K1356 • K1356} {g' = ε} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00688.proved (MV00688.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
