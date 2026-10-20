{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij671345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01797 as MV01797
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01798 as MV01798
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X67 • K1345 ≈ K1345 • X67
proved = GL.•-cancelʳ {g = X67 • K1345} {g' = K1345 • X67} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01797.proved (MV01798.proved))) (trans (cong refl Base.proved) (move-product MV01798.proved (MV01797.proved))))
