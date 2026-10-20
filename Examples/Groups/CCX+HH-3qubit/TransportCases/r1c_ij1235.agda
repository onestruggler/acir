{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij1235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1235 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00676 as MV00676
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K1235 • K1235 ≈ ε
proved = GL.•-cancelʳ {g = K1235 • K1235} {g' = ε} {h = p (s0 • s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV00676.proved (MV00676.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
