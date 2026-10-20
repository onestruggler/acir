{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij1256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1256 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00682 as MV00682
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K1256 • K1256 ≈ ε
proved = GL.•-cancelʳ {g = K1256 • K1256} {g' = ε} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00682.proved (MV00682.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
