{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; M0 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00663 as MV00663
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02871 as MV02871
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02872 as MV02872
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X25 • K0257 ≈ M0 • K0257 • M0 • K0257 • M0
proved = GL.•-cancelʳ {g = X25 • K0257} {g' = M0 • K0257 • M0 • K0257 • M0} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02871.proved (MV00663.proved))) (trans (cong refl Base.proved) (move-product MV02872.proved (move-product MV00663.proved (move-product MV02872.proved (move-product MV00663.proved (MV02872.proved)))))))
