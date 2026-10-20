{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij012467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; K0126 ; K1467 ; K2467 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01774 as MV01774
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03053 as MV03053
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03054 as MV03054
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03055 as MV03055
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K0124 • K1467 ≈ K2467 • K0126
proved = GL.•-cancelʳ {g = K0124 • K1467} {g' = K2467 • K0126} {h = p (s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01774.proved (MV03053.proved))) (trans (cong refl Base.proved) (move-product MV03054.proved (MV03055.proved))))
