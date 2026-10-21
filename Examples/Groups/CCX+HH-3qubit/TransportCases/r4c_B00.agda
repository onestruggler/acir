{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0126 ; K0127 ; K0134 ; K0135 ; K0136 ; K0137 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0234 ; K0235 ; K0236 ; K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0267 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1234 ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1267 ; K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; K1367 ; K1456 ; K1457 ; K1467 ; K1567 ; K2345 ; K2346 ; X13 ; X14 ; X15 ; X16 ; X17 ; X23 ; X24 ; X25 ; X26 ; X27 ; X34 ; X35 ; X36 ; X37 ; X45 ; X46 ; X47 ; X56 ; X57 ; X67 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00113)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00147)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00641 ; module MV00642 ; module MV00643)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B017 using (module MV00644 ; module MV00645 ; module MV00646 ; module MV00647 ; module MV00648 ; module MV00649 ; module MV00650 ; module MV00651 ; module MV00652 ; module MV00653 ; module MV00654 ; module MV00655 ; module MV00656 ; module MV00657 ; module MV00658 ; module MV00659 ; module MV00660 ; module MV00661 ; module MV00662 ; module MV00663 ; module MV00664 ; module MV00665 ; module MV00666 ; module MV00667 ; module MV00668 ; module MV00669 ; module MV00670 ; module MV00671 ; module MV00672 ; module MV00673 ; module MV00674 ; module MV00675 ; module MV00676 ; module MV00677 ; module MV00678 ; module MV00679 ; module MV00680 ; module MV00681 ; module MV00682 ; module MV00683 ; module MV00684 ; module MV00685 ; module MV00686 ; module MV00687 ; module MV00688 ; module MV00689 ; module MV00690)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B018 using (module MV00691 ; module MV00692 ; module MV00693 ; module MV00694 ; module MV00695 ; module MV00696)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B065 using (module MV02556 ; module MV02560 ; module MV02564 ; module MV02568)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B066 using (module MV02572 ; module MV02576 ; module MV02580 ; module MV02584 ; module MV02588 ; module MV02592 ; module MV02596 ; module MV02600 ; module MV02604 ; module MV02608 ; module MV02612 ; module MV02616 ; module MV02620 ; module MV02624 ; module MV02628 ; module MV02632)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B067 using (module MV02636 ; module MV02640 ; module MV02644 ; module MV02648 ; module MV02652 ; module MV02656 ; module MV02660 ; module MV02664 ; module MV02668 ; module MV02672 ; module MV02676)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B068 using (module MV02680 ; module MV02684 ; module MV02688 ; module MV02692 ; module MV02696 ; module MV02700 ; module MV02704 ; module MV02708 ; module MV02712 ; module MV02716 ; module MV02720)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B069 using (module MV02724 ; module MV02728 ; module MV02732 ; module MV02736 ; module MV02740 ; module MV02744 ; module MV02748 ; module MV02752 ; module MV02756 ; module MV02760)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B070 using (module MV02764 ; module MV02768 ; module MV02772 ; module MV02776)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B075 using (module MV02963 ; module MV02964 ; module MV02965 ; module MV02966 ; module MV02967 ; module MV02968 ; module MV02969 ; module MV02970 ; module MV02971 ; module MV02972 ; module MV02973 ; module MV02974 ; module MV02975 ; module MV02976 ; module MV02977 ; module MV02978 ; module MV02979 ; module MV02980 ; module MV02981 ; module MV02982 ; module MV02983 ; module MV02984 ; module MV02985 ; module MV02986 ; module MV02987 ; module MV02988 ; module MV02989 ; module MV02990 ; module MV02991 ; module MV02992 ; module MV02993 ; module MV02994 ; module MV02995 ; module MV02996 ; module MV02997 ; module MV02998)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B076 using (module MV02999 ; module MV03000 ; module MV03001 ; module MV03002 ; module MV03003 ; module MV03004 ; module MV03005 ; module MV03006 ; module MV03007 ; module MV03008 ; module MV03009 ; module MV03010 ; module MV03011 ; module MV03012 ; module MV03013 ; module MV03014 ; module MV03015 ; module MV03016 ; module MV03017 ; module MV03018)
open import Examples.Groups.CCX+HH-3qubit.FrameRelations.B000 using (module R099)

module r4c_ij0123 where

  proved : X23 • K0123 ≈ K0123 • X13
  proved = GL.•-cancelʳ {g = X23 • K0123} {g' = K0123 • X13} {h = p (ε)}
    (trans (sym (move-product MV02963.proved (MV00641.proved))) (trans (cong refl R099.proved) (move-product MV00641.proved (MV02556.proved))))

module r4c_ij0124 where

  proved : X24 • K0124 ≈ K0124 • X14
  proved = GL.•-cancelʳ {g = X24 • K0124} {g' = K0124 • X14} {h = p (s3)}
    (trans (sym (move-product MV00147.proved (MV00245.proved))) (trans (cong refl R099.proved) (move-product MV00245.proved (MV00113.proved))))

module r4c_ij0125 where

  proved : X25 • K0125 ≈ K0125 • X15
  proved = GL.•-cancelʳ {g = X25 • K0125} {g' = K0125 • X15} {h = p (s4 • s3)}
    (trans (sym (move-product MV02964.proved (MV00642.proved))) (trans (cong refl R099.proved) (move-product MV00642.proved (MV02560.proved))))

module r4c_ij0126 where

  proved : X26 • K0126 ≈ K0126 • X16
  proved = GL.•-cancelʳ {g = X26 • K0126} {g' = K0126 • X16} {h = p (s5 • s4 • s3)}
    (trans (sym (move-product MV02965.proved (MV00643.proved))) (trans (cong refl R099.proved) (move-product MV00643.proved (MV02564.proved))))

module r4c_ij0127 where

  proved : X27 • K0127 ≈ K0127 • X17
  proved = GL.•-cancelʳ {g = X27 • K0127} {g' = K0127 • X17} {h = p (s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02966.proved (MV00644.proved))) (trans (cong refl R099.proved) (move-product MV00644.proved (MV02568.proved))))

module r4c_ij0134 where

  proved : X34 • K0134 ≈ K0134 • X14
  proved = GL.•-cancelʳ {g = X34 • K0134} {g' = K0134 • X14} {h = p (s2 • s3)}
    (trans (sym (move-product MV02967.proved (MV00645.proved))) (trans (cong refl R099.proved) (move-product MV00645.proved (MV02572.proved))))

module r4c_ij0135 where

  proved : X35 • K0135 ≈ K0135 • X15
  proved = GL.•-cancelʳ {g = X35 • K0135} {g' = K0135 • X15} {h = p (s2 • s4 • s3)}
    (trans (sym (move-product MV02968.proved (MV00646.proved))) (trans (cong refl R099.proved) (move-product MV00646.proved (MV02576.proved))))

module r4c_ij0136 where

  proved : X36 • K0136 ≈ K0136 • X16
  proved = GL.•-cancelʳ {g = X36 • K0136} {g' = K0136 • X16} {h = p (s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02969.proved (MV00647.proved))) (trans (cong refl R099.proved) (move-product MV00647.proved (MV02580.proved))))

module r4c_ij0137 where

  proved : X37 • K0137 ≈ K0137 • X17
  proved = GL.•-cancelʳ {g = X37 • K0137} {g' = K0137 • X17} {h = p (s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02970.proved (MV00648.proved))) (trans (cong refl R099.proved) (move-product MV00648.proved (MV02584.proved))))

module r4c_ij0145 where

  proved : X45 • K0145 ≈ K0145 • X15
  proved = GL.•-cancelʳ {g = X45 • K0145} {g' = K0145 • X15} {h = p (s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV02971.proved (MV00649.proved))) (trans (cong refl R099.proved) (move-product MV00649.proved (MV02588.proved))))

module r4c_ij0146 where

  proved : X46 • K0146 ≈ K0146 • X16
  proved = GL.•-cancelʳ {g = X46 • K0146} {g' = K0146 • X16} {h = p (s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02972.proved (MV00650.proved))) (trans (cong refl R099.proved) (move-product MV00650.proved (MV02592.proved))))

module r4c_ij0147 where

  proved : X47 • K0147 ≈ K0147 • X17
  proved = GL.•-cancelʳ {g = X47 • K0147} {g' = K0147 • X17} {h = p (s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02973.proved (MV00651.proved))) (trans (cong refl R099.proved) (move-product MV00651.proved (MV02596.proved))))

module r4c_ij0156 where

  proved : X56 • K0156 ≈ K0156 • X16
  proved = GL.•-cancelʳ {g = X56 • K0156} {g' = K0156 • X16} {h = p (s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02974.proved (MV00652.proved))) (trans (cong refl R099.proved) (move-product MV00652.proved (MV02600.proved))))

module r4c_ij0157 where

  proved : X57 • K0157 ≈ K0157 • X17
  proved = GL.•-cancelʳ {g = X57 • K0157} {g' = K0157 • X17} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02975.proved (MV00653.proved))) (trans (cong refl R099.proved) (move-product MV00653.proved (MV02604.proved))))

module r4c_ij0167 where

  proved : X67 • K0167 ≈ K0167 • X17
  proved = GL.•-cancelʳ {g = X67 • K0167} {g' = K0167 • X17} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02976.proved (MV00654.proved))) (trans (cong refl R099.proved) (move-product MV00654.proved (MV02608.proved))))

module r4c_ij0234 where

  proved : X34 • K0234 ≈ K0234 • X24
  proved = GL.•-cancelʳ {g = X34 • K0234} {g' = K0234 • X24} {h = p (s1 • s2 • s3)}
    (trans (sym (move-product MV02977.proved (MV00655.proved))) (trans (cong refl R099.proved) (move-product MV00655.proved (MV02612.proved))))

module r4c_ij0235 where

  proved : X35 • K0235 ≈ K0235 • X25
  proved = GL.•-cancelʳ {g = X35 • K0235} {g' = K0235 • X25} {h = p (s1 • s2 • s4 • s3)}
    (trans (sym (move-product MV02978.proved (MV00656.proved))) (trans (cong refl R099.proved) (move-product MV00656.proved (MV02616.proved))))

module r4c_ij0236 where

  proved : X36 • K0236 ≈ K0236 • X26
  proved = GL.•-cancelʳ {g = X36 • K0236} {g' = K0236 • X26} {h = p (s1 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02979.proved (MV00657.proved))) (trans (cong refl R099.proved) (move-product MV00657.proved (MV02620.proved))))

module r4c_ij0237 where

  proved : X37 • K0237 ≈ K0237 • X27
  proved = GL.•-cancelʳ {g = X37 • K0237} {g' = K0237 • X27} {h = p (s1 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02980.proved (MV00658.proved))) (trans (cong refl R099.proved) (move-product MV00658.proved (MV02624.proved))))

module r4c_ij0245 where

  proved : X45 • K0245 ≈ K0245 • X25
  proved = GL.•-cancelʳ {g = X45 • K0245} {g' = K0245 • X25} {h = p (s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV02981.proved (MV00659.proved))) (trans (cong refl R099.proved) (move-product MV00659.proved (MV02628.proved))))

module r4c_ij0246 where

  proved : X46 • K0246 ≈ K0246 • X26
  proved = GL.•-cancelʳ {g = X46 • K0246} {g' = K0246 • X26} {h = p (s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02982.proved (MV00660.proved))) (trans (cong refl R099.proved) (move-product MV00660.proved (MV02632.proved))))

module r4c_ij0247 where

  proved : X47 • K0247 ≈ K0247 • X27
  proved = GL.•-cancelʳ {g = X47 • K0247} {g' = K0247 • X27} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02983.proved (MV00661.proved))) (trans (cong refl R099.proved) (move-product MV00661.proved (MV02636.proved))))

module r4c_ij0256 where

  proved : X56 • K0256 ≈ K0256 • X26
  proved = GL.•-cancelʳ {g = X56 • K0256} {g' = K0256 • X26} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02984.proved (MV00662.proved))) (trans (cong refl R099.proved) (move-product MV00662.proved (MV02640.proved))))

module r4c_ij0257 where

  proved : X57 • K0257 ≈ K0257 • X27
  proved = GL.•-cancelʳ {g = X57 • K0257} {g' = K0257 • X27} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02985.proved (MV00663.proved))) (trans (cong refl R099.proved) (move-product MV00663.proved (MV02644.proved))))

module r4c_ij0267 where

  proved : X67 • K0267 ≈ K0267 • X27
  proved = GL.•-cancelʳ {g = X67 • K0267} {g' = K0267 • X27} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02986.proved (MV00664.proved))) (trans (cong refl R099.proved) (move-product MV00664.proved (MV02648.proved))))

module r4c_ij0345 where

  proved : X45 • K0345 ≈ K0345 • X35
  proved = GL.•-cancelʳ {g = X45 • K0345} {g' = K0345 • X35} {h = p (s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV02987.proved (MV00665.proved))) (trans (cong refl R099.proved) (move-product MV00665.proved (MV02652.proved))))

module r4c_ij0346 where

  proved : X46 • K0346 ≈ K0346 • X36
  proved = GL.•-cancelʳ {g = X46 • K0346} {g' = K0346 • X36} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02988.proved (MV00666.proved))) (trans (cong refl R099.proved) (move-product MV00666.proved (MV02656.proved))))

module r4c_ij0347 where

  proved : X47 • K0347 ≈ K0347 • X37
  proved = GL.•-cancelʳ {g = X47 • K0347} {g' = K0347 • X37} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02989.proved (MV00667.proved))) (trans (cong refl R099.proved) (move-product MV00667.proved (MV02660.proved))))

module r4c_ij0356 where

  proved : X56 • K0356 ≈ K0356 • X36
  proved = GL.•-cancelʳ {g = X56 • K0356} {g' = K0356 • X36} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02990.proved (MV00668.proved))) (trans (cong refl R099.proved) (move-product MV00668.proved (MV02664.proved))))

module r4c_ij0357 where

  proved : X57 • K0357 ≈ K0357 • X37
  proved = GL.•-cancelʳ {g = X57 • K0357} {g' = K0357 • X37} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02991.proved (MV00669.proved))) (trans (cong refl R099.proved) (move-product MV00669.proved (MV02668.proved))))

module r4c_ij0367 where

  proved : X67 • K0367 ≈ K0367 • X37
  proved = GL.•-cancelʳ {g = X67 • K0367} {g' = K0367 • X37} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02992.proved (MV00670.proved))) (trans (cong refl R099.proved) (move-product MV00670.proved (MV02672.proved))))

module r4c_ij0456 where

  proved : X56 • K0456 ≈ K0456 • X46
  proved = GL.•-cancelʳ {g = X56 • K0456} {g' = K0456 • X46} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02993.proved (MV00671.proved))) (trans (cong refl R099.proved) (move-product MV00671.proved (MV02676.proved))))

module r4c_ij0457 where

  proved : X57 • K0457 ≈ K0457 • X47
  proved = GL.•-cancelʳ {g = X57 • K0457} {g' = K0457 • X47} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02994.proved (MV00672.proved))) (trans (cong refl R099.proved) (move-product MV00672.proved (MV02680.proved))))

module r4c_ij0467 where

  proved : X67 • K0467 ≈ K0467 • X47
  proved = GL.•-cancelʳ {g = X67 • K0467} {g' = K0467 • X47} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02995.proved (MV00673.proved))) (trans (cong refl R099.proved) (move-product MV00673.proved (MV02684.proved))))

module r4c_ij0567 where

  proved : X67 • K0567 ≈ K0567 • X57
  proved = GL.•-cancelʳ {g = X67 • K0567} {g' = K0567 • X57} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02996.proved (MV00674.proved))) (trans (cong refl R099.proved) (move-product MV00674.proved (MV02688.proved))))

module r4c_ij1234 where

  proved : X34 • K1234 ≈ K1234 • X24
  proved = GL.•-cancelʳ {g = X34 • K1234} {g' = K1234 • X24} {h = p (s0 • s1 • s2 • s3)}
    (trans (sym (move-product MV02997.proved (MV00675.proved))) (trans (cong refl R099.proved) (move-product MV00675.proved (MV02692.proved))))

module r4c_ij1235 where

  proved : X35 • K1235 ≈ K1235 • X25
  proved = GL.•-cancelʳ {g = X35 • K1235} {g' = K1235 • X25} {h = p (s0 • s1 • s2 • s4 • s3)}
    (trans (sym (move-product MV02998.proved (MV00676.proved))) (trans (cong refl R099.proved) (move-product MV00676.proved (MV02696.proved))))

module r4c_ij1236 where

  proved : X36 • K1236 ≈ K1236 • X26
  proved = GL.•-cancelʳ {g = X36 • K1236} {g' = K1236 • X26} {h = p (s0 • s1 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02999.proved (MV00677.proved))) (trans (cong refl R099.proved) (move-product MV00677.proved (MV02700.proved))))

module r4c_ij1237 where

  proved : X37 • K1237 ≈ K1237 • X27
  proved = GL.•-cancelʳ {g = X37 • K1237} {g' = K1237 • X27} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03000.proved (MV00678.proved))) (trans (cong refl R099.proved) (move-product MV00678.proved (MV02704.proved))))

module r4c_ij1245 where

  proved : X45 • K1245 ≈ K1245 • X25
  proved = GL.•-cancelʳ {g = X45 • K1245} {g' = K1245 • X25} {h = p (s0 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV03001.proved (MV00679.proved))) (trans (cong refl R099.proved) (move-product MV00679.proved (MV02708.proved))))

module r4c_ij1246 where

  proved : X46 • K1246 ≈ K1246 • X26
  proved = GL.•-cancelʳ {g = X46 • K1246} {g' = K1246 • X26} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV03002.proved (MV00680.proved))) (trans (cong refl R099.proved) (move-product MV00680.proved (MV02712.proved))))

module r4c_ij1247 where

  proved : X47 • K1247 ≈ K1247 • X27
  proved = GL.•-cancelʳ {g = X47 • K1247} {g' = K1247 • X27} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03003.proved (MV00681.proved))) (trans (cong refl R099.proved) (move-product MV00681.proved (MV02716.proved))))

module r4c_ij1256 where

  proved : X56 • K1256 ≈ K1256 • X26
  proved = GL.•-cancelʳ {g = X56 • K1256} {g' = K1256 • X26} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV03004.proved (MV00682.proved))) (trans (cong refl R099.proved) (move-product MV00682.proved (MV02720.proved))))

module r4c_ij1257 where

  proved : X57 • K1257 ≈ K1257 • X27
  proved = GL.•-cancelʳ {g = X57 • K1257} {g' = K1257 • X27} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03005.proved (MV00683.proved))) (trans (cong refl R099.proved) (move-product MV00683.proved (MV02724.proved))))

module r4c_ij1267 where

  proved : X67 • K1267 ≈ K1267 • X27
  proved = GL.•-cancelʳ {g = X67 • K1267} {g' = K1267 • X27} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03006.proved (MV00684.proved))) (trans (cong refl R099.proved) (move-product MV00684.proved (MV02728.proved))))

module r4c_ij1345 where

  proved : X45 • K1345 ≈ K1345 • X35
  proved = GL.•-cancelʳ {g = X45 • K1345} {g' = K1345 • X35} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV03007.proved (MV00685.proved))) (trans (cong refl R099.proved) (move-product MV00685.proved (MV02732.proved))))

module r4c_ij1346 where

  proved : X46 • K1346 ≈ K1346 • X36
  proved = GL.•-cancelʳ {g = X46 • K1346} {g' = K1346 • X36} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV03008.proved (MV00686.proved))) (trans (cong refl R099.proved) (move-product MV00686.proved (MV02736.proved))))

module r4c_ij1347 where

  proved : X47 • K1347 ≈ K1347 • X37
  proved = GL.•-cancelʳ {g = X47 • K1347} {g' = K1347 • X37} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03009.proved (MV00687.proved))) (trans (cong refl R099.proved) (move-product MV00687.proved (MV02740.proved))))

module r4c_ij1356 where

  proved : X56 • K1356 ≈ K1356 • X36
  proved = GL.•-cancelʳ {g = X56 • K1356} {g' = K1356 • X36} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV03010.proved (MV00688.proved))) (trans (cong refl R099.proved) (move-product MV00688.proved (MV02744.proved))))

module r4c_ij1357 where

  proved : X57 • K1357 ≈ K1357 • X37
  proved = GL.•-cancelʳ {g = X57 • K1357} {g' = K1357 • X37} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03011.proved (MV00689.proved))) (trans (cong refl R099.proved) (move-product MV00689.proved (MV02748.proved))))

module r4c_ij1367 where

  proved : X67 • K1367 ≈ K1367 • X37
  proved = GL.•-cancelʳ {g = X67 • K1367} {g' = K1367 • X37} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03012.proved (MV00690.proved))) (trans (cong refl R099.proved) (move-product MV00690.proved (MV02752.proved))))

module r4c_ij1456 where

  proved : X56 • K1456 ≈ K1456 • X46
  proved = GL.•-cancelʳ {g = X56 • K1456} {g' = K1456 • X46} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV03013.proved (MV00691.proved))) (trans (cong refl R099.proved) (move-product MV00691.proved (MV02756.proved))))

module r4c_ij1457 where

  proved : X57 • K1457 ≈ K1457 • X47
  proved = GL.•-cancelʳ {g = X57 • K1457} {g' = K1457 • X47} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03014.proved (MV00692.proved))) (trans (cong refl R099.proved) (move-product MV00692.proved (MV02760.proved))))

module r4c_ij1467 where

  proved : X67 • K1467 ≈ K1467 • X47
  proved = GL.•-cancelʳ {g = X67 • K1467} {g' = K1467 • X47} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03015.proved (MV00693.proved))) (trans (cong refl R099.proved) (move-product MV00693.proved (MV02764.proved))))

module r4c_ij1567 where

  proved : X67 • K1567 ≈ K1567 • X57
  proved = GL.•-cancelʳ {g = X67 • K1567} {g' = K1567 • X57} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV03016.proved (MV00694.proved))) (trans (cong refl R099.proved) (move-product MV00694.proved (MV02768.proved))))

module r4c_ij2345 where

  proved : X45 • K2345 ≈ K2345 • X35
  proved = GL.•-cancelʳ {g = X45 • K2345} {g' = K2345 • X35} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV03017.proved (MV00695.proved))) (trans (cong refl R099.proved) (move-product MV00695.proved (MV02772.proved))))

module r4c_ij2346 where

  proved : X46 • K2346 ≈ K2346 • X36
  proved = GL.•-cancelʳ {g = X46 • K2346} {g' = K2346 • X36} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV03018.proved (MV00696.proved))) (trans (cong refl R099.proved) (move-product MV00696.proved (MV02776.proved))))
