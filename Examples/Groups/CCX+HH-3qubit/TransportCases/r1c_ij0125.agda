{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0125 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0125 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s3 ; s4 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00642 as MV00642
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0125 • K0125 ≈ ε
proved = GL.•-cancelʳ {g = K0125 • K0125} {g' = ε} {h = p (s4 • s3)}
  (trans (sym (move-product MV00642.proved (MV00642.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
