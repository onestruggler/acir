{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij1236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1236 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00677 as MV00677
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K1236 • K1236 ≈ ε
proved = GL.•-cancelʳ {g = K1236 • K1236} {g' = ε} {h = p (s0 • s1 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00677.proved (MV00677.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
