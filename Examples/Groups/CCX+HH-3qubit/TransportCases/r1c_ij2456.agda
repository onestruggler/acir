{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij2456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2456 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00701 as MV00701
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K2456 • K2456 ≈ ε
proved = GL.•-cancelʳ {g = K2456 • K2456} {g' = ε} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00701.proved (MV00701.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
