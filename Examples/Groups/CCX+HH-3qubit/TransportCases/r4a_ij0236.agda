{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0236 ; M2 ; M6 ; X02 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00657 as MV00657
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02619 as MV02619
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02620 as MV02620
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02621 as MV02621
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02622 as MV02622
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X02 • K0236 ≈ K0236 • X26 • M2 • M6
proved = GL.•-cancelʳ {g = X02 • K0236} {g' = K0236 • X26 • M2 • M6} {h = p (s1 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02619.proved (MV00657.proved))) (trans (cong refl Base.proved) (move-product MV00657.proved (move-product MV02620.proved (move-product MV02621.proved (MV02622.proved))))))
