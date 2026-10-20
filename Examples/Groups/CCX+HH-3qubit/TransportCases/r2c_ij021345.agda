{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij021345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; X02 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00685 as MV00685
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01049 as MV01049
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X02 • K1345 ≈ K1345 • X02
proved = GL.•-cancelʳ {g = X02 • K1345} {g' = K1345 • X02} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV01049.proved (MV00685.proved))) (trans (cong refl Base.proved) (move-product MV00685.proved (MV01049.proved))))
