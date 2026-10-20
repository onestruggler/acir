{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij21457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1457 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02026 as MV02026
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02027 as MV02027
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K1457 ≈ K1457 • M2
proved = GL.•-cancelʳ {g = M2 • K1457} {g' = K1457 • M2} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02026.proved (MV02027.proved))) (trans (cong refl Base.proved) (move-product MV02027.proved (MV02026.proved))))
