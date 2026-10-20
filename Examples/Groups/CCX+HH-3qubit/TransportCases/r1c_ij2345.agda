{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij2345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2345 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00695 as MV00695
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K2345 • K2345 ≈ ε
proved = GL.•-cancelʳ {g = K2345 • K2345} {g' = ε} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV00695.proved (MV00695.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
