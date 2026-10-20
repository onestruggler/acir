{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij270 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00902 as MV00902
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00903 as MV00903
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X27 • M0 ≈ M0 • X27
proved = GL.•-cancelʳ {g = X27 • M0} {g' = M0 • X27} {h = p (s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00902.proved (MV00903.proved))) (trans (cong refl Base.proved) (move-product MV00903.proved (MV00902.proved))))
