{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij451267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1267 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01647 as MV01647
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01648 as MV01648
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X45 • K1267 ≈ K1267 • X45
proved = GL.•-cancelʳ {g = X45 • K1267} {g' = K1267 • X45} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01647.proved (MV01648.proved))) (trans (cong refl Base.proved) (move-product MV01648.proved (MV01647.proved))))
