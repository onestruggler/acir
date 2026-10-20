{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s1 ; s2 ; s3 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00655 as MV00655
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0234 • K0234 ≈ ε
proved = GL.•-cancelʳ {g = K0234 • K0234} {g' = ε} {h = p (s1 • s2 • s3)}
  (trans (sym (move-product MV00655.proved (MV00655.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
