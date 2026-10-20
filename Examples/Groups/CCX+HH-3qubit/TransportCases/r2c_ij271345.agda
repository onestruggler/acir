{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij271345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01499 as MV01499
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01500 as MV01500
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X27 • K1345 ≈ K1345 • X27
proved = GL.•-cancelʳ {g = X27 • K1345} {g' = K1345 • X27} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01499.proved (MV01500.proved))) (trans (cong refl Base.proved) (move-product MV01500.proved (MV01499.proved))))
