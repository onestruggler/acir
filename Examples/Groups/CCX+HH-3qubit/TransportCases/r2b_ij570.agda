{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij570 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01010 as MV01010
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01011 as MV01011
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X57 • M0 ≈ M0 • X57
proved = GL.•-cancelʳ {g = X57 • M0} {g' = M0 • X57} {h = p (s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01010.proved (MV01011.proved))) (trans (cong refl Base.proved) (move-product MV01011.proved (MV01010.proved))))
