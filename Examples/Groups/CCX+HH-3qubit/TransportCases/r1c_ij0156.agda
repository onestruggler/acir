{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0156 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0156 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00652 as MV00652
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0156 • K0156 ≈ ε
proved = GL.•-cancelʳ {g = K0156 • K0156} {g' = ε} {h = p (s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00652.proved (MV00652.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
