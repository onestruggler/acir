{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1235 ; M1 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00676 as MV00676
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02896 as MV02896
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02897 as MV02897
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X23 • K1235 ≈ M1 • K1235 • M1 • K1235 • M1
proved = GL.•-cancelʳ {g = X23 • K1235} {g' = M1 • K1235 • M1 • K1235 • M1} {h = p (s0 • s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV02896.proved (MV00676.proved))) (trans (cong refl Base.proved) (move-product MV02897.proved (move-product MV00676.proved (move-product MV02897.proved (move-product MV00676.proved (MV02897.proved)))))))
