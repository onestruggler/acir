{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij470156 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0156 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01691 as MV01691
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01692 as MV01692
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X47 • K0156 ≈ K0156 • X47
proved = GL.•-cancelʳ {g = X47 • K0156} {g' = K0156 • X47} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01691.proved (MV01692.proved))) (trans (cong refl Base.proved) (move-product MV01692.proved (MV01691.proved))))
