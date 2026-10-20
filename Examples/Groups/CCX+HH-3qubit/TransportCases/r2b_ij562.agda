{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij562 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01002 as MV01002
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01003 as MV01003
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X56 • M2 ≈ M2 • X56
proved = GL.•-cancelʳ {g = X56 • M2} {g' = M2 • X56} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01002.proved (MV01003.proved))) (trans (cong refl Base.proved) (move-product MV01003.proved (MV01002.proved))))
