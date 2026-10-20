{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij570146 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0146 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01751 as MV01751
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01752 as MV01752
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X57 • K0146 ≈ K0146 • X57
proved = GL.•-cancelʳ {g = X57 • K0146} {g' = K0146 • X57} {h = p (s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01751.proved (MV01752.proved))) (trans (cong refl Base.proved) (move-product MV01752.proved (MV01751.proved))))
