{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij3456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3456 ; M3 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00705 as MV00705
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02954 as MV02954
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02955 as MV02955
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X45 • K3456 ≈ M3 • K3456 • M3 • K3456 • M3
proved = GL.•-cancelʳ {g = X45 • K3456} {g' = M3 • K3456 • M3 • K3456 • M3} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02954.proved (MV00705.proved))) (trans (cong refl Base.proved) (move-product MV02955.proved (move-product MV00705.proved (move-product MV02955.proved (move-product MV00705.proved (MV02955.proved)))))))
