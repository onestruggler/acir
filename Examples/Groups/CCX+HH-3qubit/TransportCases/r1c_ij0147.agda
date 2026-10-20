{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0147 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0147 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00651 as MV00651
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0147 • K0147 ≈ ε
proved = GL.•-cancelʳ {g = K0147 • K0147} {g' = ε} {h = p (s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00651.proved (MV00651.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
