{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij24670135 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; K2467 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00703 as MV00703
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02443 as MV02443
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K2467 • K0135 ≈ K0135 • K2467
proved = GL.•-cancelʳ {g = K2467 • K0135} {g' = K0135 • K2467} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00703.proved (MV02443.proved))) (trans (cong refl Base.proved) (move-product MV02443.proved (MV00703.proved))))
