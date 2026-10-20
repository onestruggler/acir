{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij571236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1236 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01763 as MV01763
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01764 as MV01764
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X57 • K1236 ≈ K1236 • X57
proved = GL.•-cancelʳ {g = X57 • K1236} {g' = K1236 • X57} {h = p (s0 • s1 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01763.proved (MV01764.proved))) (trans (cong refl Base.proved) (move-product MV01764.proved (MV01763.proved))))
