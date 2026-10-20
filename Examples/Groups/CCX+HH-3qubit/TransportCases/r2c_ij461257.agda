{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij461257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1257 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01675 as MV01675
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01676 as MV01676
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X46 • K1257 ≈ K1257 • X46
proved = GL.•-cancelʳ {g = X46 • K1257} {g' = K1257 • X46} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01675.proved (MV01676.proved))) (trans (cong refl Base.proved) (move-product MV01676.proved (MV01675.proved))))
