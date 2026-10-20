{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0235 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00656 as MV00656
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0235 • K0235 ≈ ε
proved = GL.•-cancelʳ {g = K0235 • K0235} {g' = ε} {h = p (s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV00656.proved (MV00656.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
