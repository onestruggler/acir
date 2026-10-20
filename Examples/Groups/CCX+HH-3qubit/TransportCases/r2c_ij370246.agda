{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij370246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0246 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01608 as MV01608
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01609 as MV01609
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X37 • K0246 ≈ K0246 • X37
proved = GL.•-cancelʳ {g = X37 • K0246} {g' = K0246 • X37} {h = p (s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01608.proved (MV01609.proved))) (trans (cong refl Base.proved) (move-product MV01609.proved (MV01608.proved))))
