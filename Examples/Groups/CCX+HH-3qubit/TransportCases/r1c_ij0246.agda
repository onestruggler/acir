{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0246 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00660 as MV00660
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0246 • K0246 ≈ ε
proved = GL.•-cancelʳ {g = K0246 • K0246} {g' = ε} {h = p (s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00660.proved (MV00660.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
