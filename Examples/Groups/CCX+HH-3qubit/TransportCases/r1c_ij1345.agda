{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij1345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00685 as MV00685
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K1345 • K1345 ≈ ε
proved = GL.•-cancelʳ {g = K1345 • K1345} {g' = ε} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV00685.proved (MV00685.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
