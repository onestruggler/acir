{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0124 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s3 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as MV00245
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0124 • K0124 ≈ ε
proved = GL.•-cancelʳ {g = K0124 • K0124} {g' = ε} {h = p (s3)}
  (trans (sym (move-product MV00245.proved (MV00245.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
