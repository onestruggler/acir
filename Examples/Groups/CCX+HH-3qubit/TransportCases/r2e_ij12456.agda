{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij12456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2456 ; M1 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01965 as MV01965
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01966 as MV01966
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M1 • K2456 ≈ K2456 • M1
proved = GL.•-cancelʳ {g = M1 • K2456} {g' = K2456 • M1} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV01965.proved (MV01966.proved))) (trans (cong refl Base.proved) (move-product MV01966.proved (MV01965.proved))))
