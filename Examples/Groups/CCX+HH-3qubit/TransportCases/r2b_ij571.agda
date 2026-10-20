{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij571 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01012 as MV01012
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01013 as MV01013
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X57 • M1 ≈ M1 • X57
proved = GL.•-cancelʳ {g = X57 • M1} {g' = M1 • X57} {h = p (s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01012.proved (MV01013.proved))) (trans (cong refl Base.proved) (move-product MV01013.proved (MV01012.proved))))
