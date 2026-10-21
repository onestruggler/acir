{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_B01 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2347 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K3567 ; K4567 ; X36 ; X37 ; X46 ; X47 ; X56 ; X57 ; X67 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00632)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B018 using (module MV00697 ; module MV00698 ; module MV00699 ; module MV00700 ; module MV00701 ; module MV00702 ; module MV00703 ; module MV00704 ; module MV00705 ; module MV00706 ; module MV00707 ; module MV00708)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B070 using (module MV02780 ; module MV02784 ; module MV02788 ; module MV02792)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B071 using (module MV02796 ; module MV02800 ; module MV02804 ; module MV02808 ; module MV02812 ; module MV02816 ; module MV02820 ; module MV02824)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B072 using (module MV02828)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B076 using (module MV03019 ; module MV03020 ; module MV03021 ; module MV03022 ; module MV03023 ; module MV03024 ; module MV03025 ; module MV03026 ; module MV03027 ; module MV03028 ; module MV03029 ; module MV03030 ; module MV03031)
open import Examples.Groups.CCX+HH-3qubit.FrameRelations.B000 using (module R099)

module r4c_ij2347 where

  proved : X47 • K2347 ≈ K2347 • X37
  proved = GL.•-cancelʳ {g = X47 • K2347} {g' = K2347 • X37} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03019.proved (MV00697.proved))) (trans (cong refl R099.proved) (move-product MV00697.proved (MV02780.proved))))

module r4c_ij2356 where

  proved : X56 • K2356 ≈ K2356 • X36
  proved = GL.•-cancelʳ {g = X56 • K2356} {g' = K2356 • X36} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV03020.proved (MV00698.proved))) (trans (cong refl R099.proved) (move-product MV00698.proved (MV02784.proved))))

module r4c_ij2357 where

  proved : X57 • K2357 ≈ K2357 • X37
  proved = GL.•-cancelʳ {g = X57 • K2357} {g' = K2357 • X37} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03021.proved (MV00699.proved))) (trans (cong refl R099.proved) (move-product MV00699.proved (MV02788.proved))))

module r4c_ij2367 where

  proved : X67 • K2367 ≈ K2367 • X37
  proved = GL.•-cancelʳ {g = X67 • K2367} {g' = K2367 • X37} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03022.proved (MV00700.proved))) (trans (cong refl R099.proved) (move-product MV00700.proved (MV02792.proved))))

module r4c_ij2456 where

  proved : X56 • K2456 ≈ K2456 • X46
  proved = GL.•-cancelʳ {g = X56 • K2456} {g' = K2456 • X46} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV03023.proved (MV00701.proved))) (trans (cong refl R099.proved) (move-product MV00701.proved (MV02796.proved))))

module r4c_ij2457 where

  proved : X57 • K2457 ≈ K2457 • X47
  proved = GL.•-cancelʳ {g = X57 • K2457} {g' = K2457 • X47} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03024.proved (MV00702.proved))) (trans (cong refl R099.proved) (move-product MV00702.proved (MV02800.proved))))

module r4c_ij2467 where

  proved : X67 • K2467 ≈ K2467 • X47
  proved = GL.•-cancelʳ {g = X67 • K2467} {g' = K2467 • X47} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03025.proved (MV00703.proved))) (trans (cong refl R099.proved) (move-product MV00703.proved (MV02804.proved))))

module r4c_ij2567 where

  proved : X67 • K2567 ≈ K2567 • X57
  proved = GL.•-cancelʳ {g = X67 • K2567} {g' = K2567 • X57} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03026.proved (MV00704.proved))) (trans (cong refl R099.proved) (move-product MV00704.proved (MV02808.proved))))

module r4c_ij3456 where

  proved : X56 • K3456 ≈ K3456 • X46
  proved = GL.•-cancelʳ {g = X56 • K3456} {g' = K3456 • X46} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV03027.proved (MV00705.proved))) (trans (cong refl R099.proved) (move-product MV00705.proved (MV02812.proved))))

module r4c_ij3457 where

  proved : X57 • K3457 ≈ K3457 • X47
  proved = GL.•-cancelʳ {g = X57 • K3457} {g' = K3457 • X47} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03028.proved (MV00706.proved))) (trans (cong refl R099.proved) (move-product MV00706.proved (MV02816.proved))))

module r4c_ij3467 where

  proved : X67 • K3467 ≈ K3467 • X47
  proved = GL.•-cancelʳ {g = X67 • K3467} {g' = K3467 • X47} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03029.proved (MV00707.proved))) (trans (cong refl R099.proved) (move-product MV00707.proved (MV02820.proved))))

module r4c_ij3567 where

  proved : X67 • K3567 ≈ K3567 • X57
  proved = GL.•-cancelʳ {g = X67 • K3567} {g' = K3567 • X57} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03030.proved (MV00708.proved))) (trans (cong refl R099.proved) (move-product MV00708.proved (MV02824.proved))))

module r4c_ij4567 where

  proved : X67 • K4567 ≈ K4567 • X57
  proved = GL.•-cancelʳ {g = X67 • K4567} {g' = K4567 • X57} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03031.proved (MV00632.proved))) (trans (cong refl R099.proved) (move-product MV00632.proved (MV02828.proved))))
