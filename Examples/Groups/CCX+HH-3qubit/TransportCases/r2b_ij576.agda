{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij576 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01020 as MV01020
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01021 as MV01021
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X57 • M6 ≈ M6 • X57
proved = GL.•-cancelʳ {g = X57 • M6} {g' = M6 • X57} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01020.proved (MV01021.proved))) (trans (cong refl Base.proved) (move-product MV01021.proved (MV01020.proved))))
