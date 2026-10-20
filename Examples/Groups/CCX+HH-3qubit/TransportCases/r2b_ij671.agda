{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij671 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01024 as MV01024
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01025 as MV01025
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X67 • M1 ≈ M1 • X67
proved = GL.•-cancelʳ {g = X67 • M1} {g' = M1 • X67} {h = p (s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01024.proved (MV01025.proved))) (trans (cong refl Base.proved) (move-product MV01025.proved (MV01024.proved))))
