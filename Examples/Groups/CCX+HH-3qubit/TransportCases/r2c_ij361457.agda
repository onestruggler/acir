{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij361457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1457 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01590 as MV01590
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01591 as MV01591
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X36 • K1457 ≈ K1457 • X36
proved = GL.•-cancelʳ {g = X36 • K1457} {g' = K1457 • X36} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01590.proved (MV01591.proved))) (trans (cong refl Base.proved) (move-product MV01591.proved (MV01590.proved))))
