{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1457 ; M4 ; M7 ; X14 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00692 as MV00692
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02759 as MV02759
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02760 as MV02760
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02761 as MV02761
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02762 as MV02762
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X14 • K1457 ≈ K1457 • X47 • M4 • M7
proved = GL.•-cancelʳ {g = X14 • K1457} {g' = K1457 • X47 • M4 • M7} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02759.proved (MV00692.proved))) (trans (cong refl Base.proved) (move-product MV00692.proved (move-product MV02760.proved (move-product MV02761.proved (MV02762.proved))))))
