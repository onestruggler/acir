{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0126 ; K0127 ; K0134 ; K0135 ; K0136 ; K0137 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0234 ; K0235 ; K0236 ; K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0267 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1234 ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1267 ; K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; K1367 ; K1456 ; K1457 ; K1467 ; K1567 ; K2345 ; K2346 ; K2347 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K3567 ; _•_ ; _≈_ ; cong ; left-unit ; module GL ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε)
open K
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as R084
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00641 ; module MV00642 ; module MV00643)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B017 using (module MV00644 ; module MV00645 ; module MV00646 ; module MV00647 ; module MV00648 ; module MV00649 ; module MV00650 ; module MV00651 ; module MV00652 ; module MV00653 ; module MV00654 ; module MV00655 ; module MV00656 ; module MV00657 ; module MV00658 ; module MV00659 ; module MV00660 ; module MV00661 ; module MV00662 ; module MV00663 ; module MV00664 ; module MV00665 ; module MV00666 ; module MV00667 ; module MV00668 ; module MV00669 ; module MV00670 ; module MV00671 ; module MV00672 ; module MV00673 ; module MV00674 ; module MV00675 ; module MV00676 ; module MV00677 ; module MV00678 ; module MV00679 ; module MV00680 ; module MV00681 ; module MV00682 ; module MV00683 ; module MV00684 ; module MV00685 ; module MV00686 ; module MV00687 ; module MV00688 ; module MV00689 ; module MV00690)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B018 using (module MV00691 ; module MV00692 ; module MV00693 ; module MV00694 ; module MV00695 ; module MV00696 ; module MV00697 ; module MV00698 ; module MV00699 ; module MV00700 ; module MV00701 ; module MV00702 ; module MV00703 ; module MV00704 ; module MV00705 ; module MV00706 ; module MV00707 ; module MV00708)

module r1c_ij0123 where

  proved : K0123 • K0123 ≈ ε
  proved = GL.•-cancelʳ {g = K0123 • K0123} {g' = ε} {h = p (ε)}
    (trans (sym (move-product MV00641.proved (MV00641.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0124 where

  proved : K0124 • K0124 ≈ ε
  proved = GL.•-cancelʳ {g = K0124 • K0124} {g' = ε} {h = p (s3)}
    (trans (sym (move-product MV00245.proved (MV00245.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0125 where

  proved : K0125 • K0125 ≈ ε
  proved = GL.•-cancelʳ {g = K0125 • K0125} {g' = ε} {h = p (s4 • s3)}
    (trans (sym (move-product MV00642.proved (MV00642.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0126 where

  proved : K0126 • K0126 ≈ ε
  proved = GL.•-cancelʳ {g = K0126 • K0126} {g' = ε} {h = p (s5 • s4 • s3)}
    (trans (sym (move-product MV00643.proved (MV00643.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0127 where

  proved : K0127 • K0127 ≈ ε
  proved = GL.•-cancelʳ {g = K0127 • K0127} {g' = ε} {h = p (s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00644.proved (MV00644.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0134 where

  proved : K0134 • K0134 ≈ ε
  proved = GL.•-cancelʳ {g = K0134 • K0134} {g' = ε} {h = p (s2 • s3)}
    (trans (sym (move-product MV00645.proved (MV00645.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0135 where

  proved : K0135 • K0135 ≈ ε
  proved = GL.•-cancelʳ {g = K0135 • K0135} {g' = ε} {h = p (s2 • s4 • s3)}
    (trans (sym (move-product MV00646.proved (MV00646.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0136 where

  proved : K0136 • K0136 ≈ ε
  proved = GL.•-cancelʳ {g = K0136 • K0136} {g' = ε} {h = p (s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00647.proved (MV00647.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0137 where

  proved : K0137 • K0137 ≈ ε
  proved = GL.•-cancelʳ {g = K0137 • K0137} {g' = ε} {h = p (s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00648.proved (MV00648.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0145 where

  proved : K0145 • K0145 ≈ ε
  proved = GL.•-cancelʳ {g = K0145 • K0145} {g' = ε} {h = p (s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV00649.proved (MV00649.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0146 where

  proved : K0146 • K0146 ≈ ε
  proved = GL.•-cancelʳ {g = K0146 • K0146} {g' = ε} {h = p (s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00650.proved (MV00650.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0147 where

  proved : K0147 • K0147 ≈ ε
  proved = GL.•-cancelʳ {g = K0147 • K0147} {g' = ε} {h = p (s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00651.proved (MV00651.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0156 where

  proved : K0156 • K0156 ≈ ε
  proved = GL.•-cancelʳ {g = K0156 • K0156} {g' = ε} {h = p (s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00652.proved (MV00652.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0157 where

  proved : K0157 • K0157 ≈ ε
  proved = GL.•-cancelʳ {g = K0157 • K0157} {g' = ε} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00653.proved (MV00653.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0167 where

  proved : K0167 • K0167 ≈ ε
  proved = GL.•-cancelʳ {g = K0167 • K0167} {g' = ε} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00654.proved (MV00654.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0234 where

  proved : K0234 • K0234 ≈ ε
  proved = GL.•-cancelʳ {g = K0234 • K0234} {g' = ε} {h = p (s1 • s2 • s3)}
    (trans (sym (move-product MV00655.proved (MV00655.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0235 where

  proved : K0235 • K0235 ≈ ε
  proved = GL.•-cancelʳ {g = K0235 • K0235} {g' = ε} {h = p (s1 • s2 • s4 • s3)}
    (trans (sym (move-product MV00656.proved (MV00656.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0236 where

  proved : K0236 • K0236 ≈ ε
  proved = GL.•-cancelʳ {g = K0236 • K0236} {g' = ε} {h = p (s1 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00657.proved (MV00657.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0237 where

  proved : K0237 • K0237 ≈ ε
  proved = GL.•-cancelʳ {g = K0237 • K0237} {g' = ε} {h = p (s1 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00658.proved (MV00658.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0245 where

  proved : K0245 • K0245 ≈ ε
  proved = GL.•-cancelʳ {g = K0245 • K0245} {g' = ε} {h = p (s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV00659.proved (MV00659.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0246 where

  proved : K0246 • K0246 ≈ ε
  proved = GL.•-cancelʳ {g = K0246 • K0246} {g' = ε} {h = p (s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00660.proved (MV00660.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0247 where

  proved : K0247 • K0247 ≈ ε
  proved = GL.•-cancelʳ {g = K0247 • K0247} {g' = ε} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00661.proved (MV00661.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0256 where

  proved : K0256 • K0256 ≈ ε
  proved = GL.•-cancelʳ {g = K0256 • K0256} {g' = ε} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00662.proved (MV00662.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0257 where

  proved : K0257 • K0257 ≈ ε
  proved = GL.•-cancelʳ {g = K0257 • K0257} {g' = ε} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00663.proved (MV00663.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0267 where

  proved : K0267 • K0267 ≈ ε
  proved = GL.•-cancelʳ {g = K0267 • K0267} {g' = ε} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00664.proved (MV00664.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0345 where

  proved : K0345 • K0345 ≈ ε
  proved = GL.•-cancelʳ {g = K0345 • K0345} {g' = ε} {h = p (s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV00665.proved (MV00665.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0346 where

  proved : K0346 • K0346 ≈ ε
  proved = GL.•-cancelʳ {g = K0346 • K0346} {g' = ε} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00666.proved (MV00666.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0347 where

  proved : K0347 • K0347 ≈ ε
  proved = GL.•-cancelʳ {g = K0347 • K0347} {g' = ε} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00667.proved (MV00667.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0356 where

  proved : K0356 • K0356 ≈ ε
  proved = GL.•-cancelʳ {g = K0356 • K0356} {g' = ε} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00668.proved (MV00668.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0357 where

  proved : K0357 • K0357 ≈ ε
  proved = GL.•-cancelʳ {g = K0357 • K0357} {g' = ε} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00669.proved (MV00669.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0367 where

  proved : K0367 • K0367 ≈ ε
  proved = GL.•-cancelʳ {g = K0367 • K0367} {g' = ε} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00670.proved (MV00670.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0456 where

  proved : K0456 • K0456 ≈ ε
  proved = GL.•-cancelʳ {g = K0456 • K0456} {g' = ε} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00671.proved (MV00671.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0457 where

  proved : K0457 • K0457 ≈ ε
  proved = GL.•-cancelʳ {g = K0457 • K0457} {g' = ε} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00672.proved (MV00672.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0467 where

  proved : K0467 • K0467 ≈ ε
  proved = GL.•-cancelʳ {g = K0467 • K0467} {g' = ε} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00673.proved (MV00673.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij0567 where

  proved : K0567 • K0567 ≈ ε
  proved = GL.•-cancelʳ {g = K0567 • K0567} {g' = ε} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00674.proved (MV00674.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1234 where

  proved : K1234 • K1234 ≈ ε
  proved = GL.•-cancelʳ {g = K1234 • K1234} {g' = ε} {h = p (s0 • s1 • s2 • s3)}
    (trans (sym (move-product MV00675.proved (MV00675.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1235 where

  proved : K1235 • K1235 ≈ ε
  proved = GL.•-cancelʳ {g = K1235 • K1235} {g' = ε} {h = p (s0 • s1 • s2 • s4 • s3)}
    (trans (sym (move-product MV00676.proved (MV00676.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1236 where

  proved : K1236 • K1236 ≈ ε
  proved = GL.•-cancelʳ {g = K1236 • K1236} {g' = ε} {h = p (s0 • s1 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00677.proved (MV00677.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1237 where

  proved : K1237 • K1237 ≈ ε
  proved = GL.•-cancelʳ {g = K1237 • K1237} {g' = ε} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00678.proved (MV00678.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1245 where

  proved : K1245 • K1245 ≈ ε
  proved = GL.•-cancelʳ {g = K1245 • K1245} {g' = ε} {h = p (s0 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV00679.proved (MV00679.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1246 where

  proved : K1246 • K1246 ≈ ε
  proved = GL.•-cancelʳ {g = K1246 • K1246} {g' = ε} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00680.proved (MV00680.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1247 where

  proved : K1247 • K1247 ≈ ε
  proved = GL.•-cancelʳ {g = K1247 • K1247} {g' = ε} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00681.proved (MV00681.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1256 where

  proved : K1256 • K1256 ≈ ε
  proved = GL.•-cancelʳ {g = K1256 • K1256} {g' = ε} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00682.proved (MV00682.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1257 where

  proved : K1257 • K1257 ≈ ε
  proved = GL.•-cancelʳ {g = K1257 • K1257} {g' = ε} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00683.proved (MV00683.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1267 where

  proved : K1267 • K1267 ≈ ε
  proved = GL.•-cancelʳ {g = K1267 • K1267} {g' = ε} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00684.proved (MV00684.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1345 where

  proved : K1345 • K1345 ≈ ε
  proved = GL.•-cancelʳ {g = K1345 • K1345} {g' = ε} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV00685.proved (MV00685.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1346 where

  proved : K1346 • K1346 ≈ ε
  proved = GL.•-cancelʳ {g = K1346 • K1346} {g' = ε} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00686.proved (MV00686.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1347 where

  proved : K1347 • K1347 ≈ ε
  proved = GL.•-cancelʳ {g = K1347 • K1347} {g' = ε} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00687.proved (MV00687.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1356 where

  proved : K1356 • K1356 ≈ ε
  proved = GL.•-cancelʳ {g = K1356 • K1356} {g' = ε} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00688.proved (MV00688.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1357 where

  proved : K1357 • K1357 ≈ ε
  proved = GL.•-cancelʳ {g = K1357 • K1357} {g' = ε} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00689.proved (MV00689.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1367 where

  proved : K1367 • K1367 ≈ ε
  proved = GL.•-cancelʳ {g = K1367 • K1367} {g' = ε} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00690.proved (MV00690.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1456 where

  proved : K1456 • K1456 ≈ ε
  proved = GL.•-cancelʳ {g = K1456 • K1456} {g' = ε} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00691.proved (MV00691.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1457 where

  proved : K1457 • K1457 ≈ ε
  proved = GL.•-cancelʳ {g = K1457 • K1457} {g' = ε} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00692.proved (MV00692.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1467 where

  proved : K1467 • K1467 ≈ ε
  proved = GL.•-cancelʳ {g = K1467 • K1467} {g' = ε} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00693.proved (MV00693.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij1567 where

  proved : K1567 • K1567 ≈ ε
  proved = GL.•-cancelʳ {g = K1567 • K1567} {g' = ε} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00694.proved (MV00694.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij2345 where

  proved : K2345 • K2345 ≈ ε
  proved = GL.•-cancelʳ {g = K2345 • K2345} {g' = ε} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV00695.proved (MV00695.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij2346 where

  proved : K2346 • K2346 ≈ ε
  proved = GL.•-cancelʳ {g = K2346 • K2346} {g' = ε} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00696.proved (MV00696.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij2347 where

  proved : K2347 • K2347 ≈ ε
  proved = GL.•-cancelʳ {g = K2347 • K2347} {g' = ε} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00697.proved (MV00697.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij2356 where

  proved : K2356 • K2356 ≈ ε
  proved = GL.•-cancelʳ {g = K2356 • K2356} {g' = ε} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00698.proved (MV00698.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij2357 where

  proved : K2357 • K2357 ≈ ε
  proved = GL.•-cancelʳ {g = K2357 • K2357} {g' = ε} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00699.proved (MV00699.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij2367 where

  proved : K2367 • K2367 ≈ ε
  proved = GL.•-cancelʳ {g = K2367 • K2367} {g' = ε} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00700.proved (MV00700.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij2456 where

  proved : K2456 • K2456 ≈ ε
  proved = GL.•-cancelʳ {g = K2456 • K2456} {g' = ε} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00701.proved (MV00701.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij2457 where

  proved : K2457 • K2457 ≈ ε
  proved = GL.•-cancelʳ {g = K2457 • K2457} {g' = ε} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00702.proved (MV00702.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij2467 where

  proved : K2467 • K2467 ≈ ε
  proved = GL.•-cancelʳ {g = K2467 • K2467} {g' = ε} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00703.proved (MV00703.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij2567 where

  proved : K2567 • K2567 ≈ ε
  proved = GL.•-cancelʳ {g = K2567 • K2567} {g' = ε} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00704.proved (MV00704.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij3456 where

  proved : K3456 • K3456 ≈ ε
  proved = GL.•-cancelʳ {g = K3456 • K3456} {g' = ε} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00705.proved (MV00705.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij3457 where

  proved : K3457 • K3457 ≈ ε
  proved = GL.•-cancelʳ {g = K3457 • K3457} {g' = ε} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00706.proved (MV00706.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij3467 where

  proved : K3467 • K3467 ≈ ε
  proved = GL.•-cancelʳ {g = K3467 • K3467} {g' = ε} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00707.proved (MV00707.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))

module r1c_ij3567 where

  proved : K3567 • K3567 ≈ ε
  proved = GL.•-cancelʳ {g = K3567 • K3567} {g' = ε} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00708.proved (MV00708.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))
