{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij250134 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00645 as MV00645
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01420 as MV01420
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X25 • K0134 ≈ K0134 • X25
proved = GL.•-cancelʳ {g = X25 • K0134} {g' = K0134 • X25} {h = p (s2 • s3)}
  (trans (sym (move-product MV01420.proved (MV00645.proved))) (trans (cong refl Base.proved) (move-product MV00645.proved (MV01420.proved))))
