{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij1234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1234 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00675 as MV00675
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K1234 • K1234 ≈ ε
proved = GL.•-cancelʳ {g = K1234 • K1234} {g' = ε} {h = p (s0 • s1 • s2 • s3)}
  (trans (sym (move-product MV00675.proved (MV00675.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
