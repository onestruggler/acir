{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0345 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00665 as MV00665
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0345 • K0345 ≈ ε
proved = GL.•-cancelʳ {g = K0345 • K0345} {g' = ε} {h = p (s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV00665.proved (MV00665.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
