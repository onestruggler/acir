{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij3457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3457 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00706 as MV00706
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K3457 • K3457 ≈ ε
proved = GL.•-cancelʳ {g = K3457 • K3457} {g' = ε} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00706.proved (MV00706.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
