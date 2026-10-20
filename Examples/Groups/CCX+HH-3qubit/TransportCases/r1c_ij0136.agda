{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0136 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0136 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00647 as MV00647
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0136 • K0136 ≈ ε
proved = GL.•-cancelʳ {g = K0136 • K0136} {g' = ε} {h = p (s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00647.proved (MV00647.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
