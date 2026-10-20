{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0256 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00662 as MV00662
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0256 • K0256 ≈ ε
proved = GL.•-cancelʳ {g = K0256 • K0256} {g' = ε} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00662.proved (MV00662.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
