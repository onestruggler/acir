{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00663 as MV00663
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0257 • K0257 ≈ ε
proved = GL.•-cancelʳ {g = K0257 • K0257} {g' = ε} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00663.proved (MV00663.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
