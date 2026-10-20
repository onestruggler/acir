{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij10234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; M1 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00655 as MV00655
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01802 as MV01802
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M1 • K0234 ≈ K0234 • M1
proved = GL.•-cancelʳ {g = M1 • K0234} {g' = K0234 • M1} {h = p (s1 • s2 • s3)}
  (trans (sym (move-product MV01802.proved (MV00655.proved))) (trans (cong refl Base.proved) (move-product MV00655.proved (MV01802.proved))))
