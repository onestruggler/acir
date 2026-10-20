{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0135 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s2 ; s3 ; s4 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00646 as MV00646
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0135 • K0135 ≈ ε
proved = GL.•-cancelʳ {g = K0135 • K0135} {g' = ε} {h = p (s2 • s4 • s3)}
  (trans (sym (move-product MV00646.proved (MV00646.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
