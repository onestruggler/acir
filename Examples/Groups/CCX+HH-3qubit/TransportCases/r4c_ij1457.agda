{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1457 ; X47 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00692 as MV00692
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02760 as MV02760
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03014 as MV03014
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X57 • K1457 ≈ K1457 • X47
proved = GL.•-cancelʳ {g = X57 • K1457} {g' = K1457 • X47} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03014.proved (MV00692.proved))) (trans (cong refl Base.proved) (move-product MV00692.proved (MV02760.proved))))
