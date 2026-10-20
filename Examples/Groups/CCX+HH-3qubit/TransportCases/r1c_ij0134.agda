{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0134 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s2 ; s3 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00645 as MV00645
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0134 • K0134 ≈ ε
proved = GL.•-cancelʳ {g = K0134 • K0134} {g' = ε} {h = p (s2 • s3)}
  (trans (sym (move-product MV00645.proved (MV00645.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
