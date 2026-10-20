{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0456 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00671 as MV00671
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0456 • K0456 ≈ ε
proved = GL.•-cancelʳ {g = K0456 • K0456} {g' = ε} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00671.proved (MV00671.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
