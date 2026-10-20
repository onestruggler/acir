{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1234 ; M1 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00675 as MV00675
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01810 as MV01810
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02895 as MV02895
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X23 • K1234 ≈ M1 • K1234 • M1 • K1234 • M1
proved = GL.•-cancelʳ {g = X23 • K1234} {g' = M1 • K1234 • M1 • K1234 • M1} {h = p (s0 • s1 • s2 • s3)}
  (trans (sym (move-product MV02895.proved (MV00675.proved))) (trans (cong refl Base.proved) (move-product MV01810.proved (move-product MV00675.proved (move-product MV01810.proved (move-product MV00675.proved (MV01810.proved)))))))
