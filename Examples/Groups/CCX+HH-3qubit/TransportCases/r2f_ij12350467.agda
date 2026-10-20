{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij12350467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0467 ; K1235 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00676 as MV00676
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02416 as MV02416
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K1235 • K0467 ≈ K0467 • K1235
proved = GL.•-cancelʳ {g = K1235 • K0467} {g' = K0467 • K1235} {h = p (s0 • s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV00676.proved (MV02416.proved))) (trans (cong refl Base.proved) (move-product MV02416.proved (MV00676.proved))))
