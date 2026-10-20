{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij170256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0256 ; X17 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01349 as MV01349
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01350 as MV01350
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X17 • K0256 ≈ K0256 • X17
proved = GL.•-cancelʳ {g = X17 • K0256} {g' = K0256 • X17} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01349.proved (MV01350.proved))) (trans (cong refl Base.proved) (move-product MV01350.proved (MV01349.proved))))
