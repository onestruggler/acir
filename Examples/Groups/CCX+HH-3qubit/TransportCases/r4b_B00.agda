{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0126 ; K0127 ; K0134 ; K0135 ; K0136 ; K0137 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0234 ; K0235 ; K0236 ; K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0267 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1234 ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1267 ; K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; M0 ; M1 ; X12 ; X13 ; X14 ; X15 ; X16 ; X23 ; X24 ; X25 ; X26 ; X34 ; X35 ; X36 ; X45 ; X46 ; X56 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00003)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00106)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00635 ; module MV00641 ; module MV00642 ; module MV00643)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B017 using (module MV00644 ; module MV00645 ; module MV00646 ; module MV00647 ; module MV00648 ; module MV00649 ; module MV00650 ; module MV00651 ; module MV00652 ; module MV00653 ; module MV00654 ; module MV00655 ; module MV00656 ; module MV00657 ; module MV00658 ; module MV00659 ; module MV00660 ; module MV00661 ; module MV00662 ; module MV00663 ; module MV00664 ; module MV00665 ; module MV00666 ; module MV00667 ; module MV00668 ; module MV00669 ; module MV00670 ; module MV00671 ; module MV00672 ; module MV00673 ; module MV00674 ; module MV00675 ; module MV00676 ; module MV00677 ; module MV00678 ; module MV00679 ; module MV00680 ; module MV00681 ; module MV00682 ; module MV00683 ; module MV00684 ; module MV00685 ; module MV00686 ; module MV00687 ; module MV00688 ; module MV00689)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B020 using (module MV00785)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B047 using (module MV01801 ; module MV01803 ; module MV01810)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B072 using (module MV02831 ; module MV02832 ; module MV02833 ; module MV02834 ; module MV02835 ; module MV02836 ; module MV02837 ; module MV02838 ; module MV02839 ; module MV02840 ; module MV02841 ; module MV02842 ; module MV02843 ; module MV02844 ; module MV02845 ; module MV02846 ; module MV02847 ; module MV02848 ; module MV02849 ; module MV02850 ; module MV02851 ; module MV02852 ; module MV02853 ; module MV02854 ; module MV02855 ; module MV02856 ; module MV02857 ; module MV02858 ; module MV02859 ; module MV02860 ; module MV02861 ; module MV02862 ; module MV02863 ; module MV02864 ; module MV02865 ; module MV02866 ; module MV02867 ; module MV02868 ; module MV02869 ; module MV02870 ; module MV02871 ; module MV02872 ; module MV02873 ; module MV02874 ; module MV02875 ; module MV02876)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B073 using (module MV02877 ; module MV02878 ; module MV02879 ; module MV02880 ; module MV02881 ; module MV02882 ; module MV02883 ; module MV02884 ; module MV02885 ; module MV02886 ; module MV02887 ; module MV02888 ; module MV02889 ; module MV02890 ; module MV02891 ; module MV02892 ; module MV02893 ; module MV02894 ; module MV02895 ; module MV02896 ; module MV02897 ; module MV02898 ; module MV02899 ; module MV02900 ; module MV02901 ; module MV02902 ; module MV02903 ; module MV02904 ; module MV02905 ; module MV02906 ; module MV02907 ; module MV02908 ; module MV02909 ; module MV02910 ; module MV02911 ; module MV02912 ; module MV02913 ; module MV02914 ; module MV02915 ; module MV02916 ; module MV02917 ; module MV02918 ; module MV02919)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B074 using (module MV02920 ; module MV02921 ; module MV02922 ; module MV02923)
open import Examples.Groups.CCX+HH-3qubit.FrameRelations.B000 using (module R098)

module r4b_ij0123 where

  proved : X12 • K0123 ≈ M0 • K0123 • M0 • K0123 • M0
  proved = GL.•-cancelʳ {g = X12 • K0123} {g' = M0 • K0123 • M0 • K0123 • M0} {h = p (ε)}
    (trans (sym (move-product MV00785.proved (MV00641.proved))) (trans (cong refl R098.proved) (move-product MV00635.proved (move-product MV00641.proved (move-product MV00635.proved (move-product MV00641.proved (MV00635.proved)))))))

module r4b_ij0124 where

  proved : X12 • K0124 ≈ M0 • K0124 • M0 • K0124 • M0
  proved = GL.•-cancelʳ {g = X12 • K0124} {g' = M0 • K0124 • M0 • K0124 • M0} {h = p (s3)}
    (trans (sym (move-product MV00106.proved (MV00245.proved))) (trans (cong refl R098.proved) (move-product MV00003.proved (move-product MV00245.proved (move-product MV00003.proved (move-product MV00245.proved (MV00003.proved)))))))

module r4b_ij0125 where

  proved : X12 • K0125 ≈ M0 • K0125 • M0 • K0125 • M0
  proved = GL.•-cancelʳ {g = X12 • K0125} {g' = M0 • K0125 • M0 • K0125 • M0} {h = p (s4 • s3)}
    (trans (sym (move-product MV02831.proved (MV00642.proved))) (trans (cong refl R098.proved) (move-product MV02832.proved (move-product MV00642.proved (move-product MV02832.proved (move-product MV00642.proved (MV02832.proved)))))))

module r4b_ij0126 where

  proved : X12 • K0126 ≈ M0 • K0126 • M0 • K0126 • M0
  proved = GL.•-cancelʳ {g = X12 • K0126} {g' = M0 • K0126 • M0 • K0126 • M0} {h = p (s5 • s4 • s3)}
    (trans (sym (move-product MV02833.proved (MV00643.proved))) (trans (cong refl R098.proved) (move-product MV02834.proved (move-product MV00643.proved (move-product MV02834.proved (move-product MV00643.proved (MV02834.proved)))))))

module r4b_ij0127 where

  proved : X12 • K0127 ≈ M0 • K0127 • M0 • K0127 • M0
  proved = GL.•-cancelʳ {g = X12 • K0127} {g' = M0 • K0127 • M0 • K0127 • M0} {h = p (s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02835.proved (MV00644.proved))) (trans (cong refl R098.proved) (move-product MV02836.proved (move-product MV00644.proved (move-product MV02836.proved (move-product MV00644.proved (MV02836.proved)))))))

module r4b_ij0134 where

  proved : X13 • K0134 ≈ M0 • K0134 • M0 • K0134 • M0
  proved = GL.•-cancelʳ {g = X13 • K0134} {g' = M0 • K0134 • M0 • K0134 • M0} {h = p (s2 • s3)}
    (trans (sym (move-product MV02837.proved (MV00645.proved))) (trans (cong refl R098.proved) (move-product MV01803.proved (move-product MV00645.proved (move-product MV01803.proved (move-product MV00645.proved (MV01803.proved)))))))

module r4b_ij0135 where

  proved : X13 • K0135 ≈ M0 • K0135 • M0 • K0135 • M0
  proved = GL.•-cancelʳ {g = X13 • K0135} {g' = M0 • K0135 • M0 • K0135 • M0} {h = p (s2 • s4 • s3)}
    (trans (sym (move-product MV02838.proved (MV00646.proved))) (trans (cong refl R098.proved) (move-product MV02839.proved (move-product MV00646.proved (move-product MV02839.proved (move-product MV00646.proved (MV02839.proved)))))))

module r4b_ij0136 where

  proved : X13 • K0136 ≈ M0 • K0136 • M0 • K0136 • M0
  proved = GL.•-cancelʳ {g = X13 • K0136} {g' = M0 • K0136 • M0 • K0136 • M0} {h = p (s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02840.proved (MV00647.proved))) (trans (cong refl R098.proved) (move-product MV02841.proved (move-product MV00647.proved (move-product MV02841.proved (move-product MV00647.proved (MV02841.proved)))))))

module r4b_ij0137 where

  proved : X13 • K0137 ≈ M0 • K0137 • M0 • K0137 • M0
  proved = GL.•-cancelʳ {g = X13 • K0137} {g' = M0 • K0137 • M0 • K0137 • M0} {h = p (s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02842.proved (MV00648.proved))) (trans (cong refl R098.proved) (move-product MV02843.proved (move-product MV00648.proved (move-product MV02843.proved (move-product MV00648.proved (MV02843.proved)))))))

module r4b_ij0145 where

  proved : X14 • K0145 ≈ M0 • K0145 • M0 • K0145 • M0
  proved = GL.•-cancelʳ {g = X14 • K0145} {g' = M0 • K0145 • M0 • K0145 • M0} {h = p (s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV02844.proved (MV00649.proved))) (trans (cong refl R098.proved) (move-product MV02845.proved (move-product MV00649.proved (move-product MV02845.proved (move-product MV00649.proved (MV02845.proved)))))))

module r4b_ij0146 where

  proved : X14 • K0146 ≈ M0 • K0146 • M0 • K0146 • M0
  proved = GL.•-cancelʳ {g = X14 • K0146} {g' = M0 • K0146 • M0 • K0146 • M0} {h = p (s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02846.proved (MV00650.proved))) (trans (cong refl R098.proved) (move-product MV02847.proved (move-product MV00650.proved (move-product MV02847.proved (move-product MV00650.proved (MV02847.proved)))))))

module r4b_ij0147 where

  proved : X14 • K0147 ≈ M0 • K0147 • M0 • K0147 • M0
  proved = GL.•-cancelʳ {g = X14 • K0147} {g' = M0 • K0147 • M0 • K0147 • M0} {h = p (s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02848.proved (MV00651.proved))) (trans (cong refl R098.proved) (move-product MV02849.proved (move-product MV00651.proved (move-product MV02849.proved (move-product MV00651.proved (MV02849.proved)))))))

module r4b_ij0156 where

  proved : X15 • K0156 ≈ M0 • K0156 • M0 • K0156 • M0
  proved = GL.•-cancelʳ {g = X15 • K0156} {g' = M0 • K0156 • M0 • K0156 • M0} {h = p (s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02850.proved (MV00652.proved))) (trans (cong refl R098.proved) (move-product MV02851.proved (move-product MV00652.proved (move-product MV02851.proved (move-product MV00652.proved (MV02851.proved)))))))

module r4b_ij0157 where

  proved : X15 • K0157 ≈ M0 • K0157 • M0 • K0157 • M0
  proved = GL.•-cancelʳ {g = X15 • K0157} {g' = M0 • K0157 • M0 • K0157 • M0} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02852.proved (MV00653.proved))) (trans (cong refl R098.proved) (move-product MV02853.proved (move-product MV00653.proved (move-product MV02853.proved (move-product MV00653.proved (MV02853.proved)))))))

module r4b_ij0167 where

  proved : X16 • K0167 ≈ M0 • K0167 • M0 • K0167 • M0
  proved = GL.•-cancelʳ {g = X16 • K0167} {g' = M0 • K0167 • M0 • K0167 • M0} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02854.proved (MV00654.proved))) (trans (cong refl R098.proved) (move-product MV02855.proved (move-product MV00654.proved (move-product MV02855.proved (move-product MV00654.proved (MV02855.proved)))))))

module r4b_ij0234 where

  proved : X23 • K0234 ≈ M0 • K0234 • M0 • K0234 • M0
  proved = GL.•-cancelʳ {g = X23 • K0234} {g' = M0 • K0234 • M0 • K0234 • M0} {h = p (s1 • s2 • s3)}
    (trans (sym (move-product MV02856.proved (MV00655.proved))) (trans (cong refl R098.proved) (move-product MV01801.proved (move-product MV00655.proved (move-product MV01801.proved (move-product MV00655.proved (MV01801.proved)))))))

module r4b_ij0235 where

  proved : X23 • K0235 ≈ M0 • K0235 • M0 • K0235 • M0
  proved = GL.•-cancelʳ {g = X23 • K0235} {g' = M0 • K0235 • M0 • K0235 • M0} {h = p (s1 • s2 • s4 • s3)}
    (trans (sym (move-product MV02857.proved (MV00656.proved))) (trans (cong refl R098.proved) (move-product MV02858.proved (move-product MV00656.proved (move-product MV02858.proved (move-product MV00656.proved (MV02858.proved)))))))

module r4b_ij0236 where

  proved : X23 • K0236 ≈ M0 • K0236 • M0 • K0236 • M0
  proved = GL.•-cancelʳ {g = X23 • K0236} {g' = M0 • K0236 • M0 • K0236 • M0} {h = p (s1 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02859.proved (MV00657.proved))) (trans (cong refl R098.proved) (move-product MV02860.proved (move-product MV00657.proved (move-product MV02860.proved (move-product MV00657.proved (MV02860.proved)))))))

module r4b_ij0237 where

  proved : X23 • K0237 ≈ M0 • K0237 • M0 • K0237 • M0
  proved = GL.•-cancelʳ {g = X23 • K0237} {g' = M0 • K0237 • M0 • K0237 • M0} {h = p (s1 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02861.proved (MV00658.proved))) (trans (cong refl R098.proved) (move-product MV02862.proved (move-product MV00658.proved (move-product MV02862.proved (move-product MV00658.proved (MV02862.proved)))))))

module r4b_ij0245 where

  proved : X24 • K0245 ≈ M0 • K0245 • M0 • K0245 • M0
  proved = GL.•-cancelʳ {g = X24 • K0245} {g' = M0 • K0245 • M0 • K0245 • M0} {h = p (s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV02863.proved (MV00659.proved))) (trans (cong refl R098.proved) (move-product MV02864.proved (move-product MV00659.proved (move-product MV02864.proved (move-product MV00659.proved (MV02864.proved)))))))

module r4b_ij0246 where

  proved : X24 • K0246 ≈ M0 • K0246 • M0 • K0246 • M0
  proved = GL.•-cancelʳ {g = X24 • K0246} {g' = M0 • K0246 • M0 • K0246 • M0} {h = p (s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02865.proved (MV00660.proved))) (trans (cong refl R098.proved) (move-product MV02866.proved (move-product MV00660.proved (move-product MV02866.proved (move-product MV00660.proved (MV02866.proved)))))))

module r4b_ij0247 where

  proved : X24 • K0247 ≈ M0 • K0247 • M0 • K0247 • M0
  proved = GL.•-cancelʳ {g = X24 • K0247} {g' = M0 • K0247 • M0 • K0247 • M0} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02867.proved (MV00661.proved))) (trans (cong refl R098.proved) (move-product MV02868.proved (move-product MV00661.proved (move-product MV02868.proved (move-product MV00661.proved (MV02868.proved)))))))

module r4b_ij0256 where

  proved : X25 • K0256 ≈ M0 • K0256 • M0 • K0256 • M0
  proved = GL.•-cancelʳ {g = X25 • K0256} {g' = M0 • K0256 • M0 • K0256 • M0} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02869.proved (MV00662.proved))) (trans (cong refl R098.proved) (move-product MV02870.proved (move-product MV00662.proved (move-product MV02870.proved (move-product MV00662.proved (MV02870.proved)))))))

module r4b_ij0257 where

  proved : X25 • K0257 ≈ M0 • K0257 • M0 • K0257 • M0
  proved = GL.•-cancelʳ {g = X25 • K0257} {g' = M0 • K0257 • M0 • K0257 • M0} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02871.proved (MV00663.proved))) (trans (cong refl R098.proved) (move-product MV02872.proved (move-product MV00663.proved (move-product MV02872.proved (move-product MV00663.proved (MV02872.proved)))))))

module r4b_ij0267 where

  proved : X26 • K0267 ≈ M0 • K0267 • M0 • K0267 • M0
  proved = GL.•-cancelʳ {g = X26 • K0267} {g' = M0 • K0267 • M0 • K0267 • M0} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02873.proved (MV00664.proved))) (trans (cong refl R098.proved) (move-product MV02874.proved (move-product MV00664.proved (move-product MV02874.proved (move-product MV00664.proved (MV02874.proved)))))))

module r4b_ij0345 where

  proved : X34 • K0345 ≈ M0 • K0345 • M0 • K0345 • M0
  proved = GL.•-cancelʳ {g = X34 • K0345} {g' = M0 • K0345 • M0 • K0345 • M0} {h = p (s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV02875.proved (MV00665.proved))) (trans (cong refl R098.proved) (move-product MV02876.proved (move-product MV00665.proved (move-product MV02876.proved (move-product MV00665.proved (MV02876.proved)))))))

module r4b_ij0346 where

  proved : X34 • K0346 ≈ M0 • K0346 • M0 • K0346 • M0
  proved = GL.•-cancelʳ {g = X34 • K0346} {g' = M0 • K0346 • M0 • K0346 • M0} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02877.proved (MV00666.proved))) (trans (cong refl R098.proved) (move-product MV02878.proved (move-product MV00666.proved (move-product MV02878.proved (move-product MV00666.proved (MV02878.proved)))))))

module r4b_ij0347 where

  proved : X34 • K0347 ≈ M0 • K0347 • M0 • K0347 • M0
  proved = GL.•-cancelʳ {g = X34 • K0347} {g' = M0 • K0347 • M0 • K0347 • M0} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02879.proved (MV00667.proved))) (trans (cong refl R098.proved) (move-product MV02880.proved (move-product MV00667.proved (move-product MV02880.proved (move-product MV00667.proved (MV02880.proved)))))))

module r4b_ij0356 where

  proved : X35 • K0356 ≈ M0 • K0356 • M0 • K0356 • M0
  proved = GL.•-cancelʳ {g = X35 • K0356} {g' = M0 • K0356 • M0 • K0356 • M0} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02881.proved (MV00668.proved))) (trans (cong refl R098.proved) (move-product MV02882.proved (move-product MV00668.proved (move-product MV02882.proved (move-product MV00668.proved (MV02882.proved)))))))

module r4b_ij0357 where

  proved : X35 • K0357 ≈ M0 • K0357 • M0 • K0357 • M0
  proved = GL.•-cancelʳ {g = X35 • K0357} {g' = M0 • K0357 • M0 • K0357 • M0} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02883.proved (MV00669.proved))) (trans (cong refl R098.proved) (move-product MV02884.proved (move-product MV00669.proved (move-product MV02884.proved (move-product MV00669.proved (MV02884.proved)))))))

module r4b_ij0367 where

  proved : X36 • K0367 ≈ M0 • K0367 • M0 • K0367 • M0
  proved = GL.•-cancelʳ {g = X36 • K0367} {g' = M0 • K0367 • M0 • K0367 • M0} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02885.proved (MV00670.proved))) (trans (cong refl R098.proved) (move-product MV02886.proved (move-product MV00670.proved (move-product MV02886.proved (move-product MV00670.proved (MV02886.proved)))))))

module r4b_ij0456 where

  proved : X45 • K0456 ≈ M0 • K0456 • M0 • K0456 • M0
  proved = GL.•-cancelʳ {g = X45 • K0456} {g' = M0 • K0456 • M0 • K0456 • M0} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02887.proved (MV00671.proved))) (trans (cong refl R098.proved) (move-product MV02888.proved (move-product MV00671.proved (move-product MV02888.proved (move-product MV00671.proved (MV02888.proved)))))))

module r4b_ij0457 where

  proved : X45 • K0457 ≈ M0 • K0457 • M0 • K0457 • M0
  proved = GL.•-cancelʳ {g = X45 • K0457} {g' = M0 • K0457 • M0 • K0457 • M0} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02889.proved (MV00672.proved))) (trans (cong refl R098.proved) (move-product MV02890.proved (move-product MV00672.proved (move-product MV02890.proved (move-product MV00672.proved (MV02890.proved)))))))

module r4b_ij0467 where

  proved : X46 • K0467 ≈ M0 • K0467 • M0 • K0467 • M0
  proved = GL.•-cancelʳ {g = X46 • K0467} {g' = M0 • K0467 • M0 • K0467 • M0} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02891.proved (MV00673.proved))) (trans (cong refl R098.proved) (move-product MV02892.proved (move-product MV00673.proved (move-product MV02892.proved (move-product MV00673.proved (MV02892.proved)))))))

module r4b_ij0567 where

  proved : X56 • K0567 ≈ M0 • K0567 • M0 • K0567 • M0
  proved = GL.•-cancelʳ {g = X56 • K0567} {g' = M0 • K0567 • M0 • K0567 • M0} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02893.proved (MV00674.proved))) (trans (cong refl R098.proved) (move-product MV02894.proved (move-product MV00674.proved (move-product MV02894.proved (move-product MV00674.proved (MV02894.proved)))))))

module r4b_ij1234 where

  proved : X23 • K1234 ≈ M1 • K1234 • M1 • K1234 • M1
  proved = GL.•-cancelʳ {g = X23 • K1234} {g' = M1 • K1234 • M1 • K1234 • M1} {h = p (s0 • s1 • s2 • s3)}
    (trans (sym (move-product MV02895.proved (MV00675.proved))) (trans (cong refl R098.proved) (move-product MV01810.proved (move-product MV00675.proved (move-product MV01810.proved (move-product MV00675.proved (MV01810.proved)))))))

module r4b_ij1235 where

  proved : X23 • K1235 ≈ M1 • K1235 • M1 • K1235 • M1
  proved = GL.•-cancelʳ {g = X23 • K1235} {g' = M1 • K1235 • M1 • K1235 • M1} {h = p (s0 • s1 • s2 • s4 • s3)}
    (trans (sym (move-product MV02896.proved (MV00676.proved))) (trans (cong refl R098.proved) (move-product MV02897.proved (move-product MV00676.proved (move-product MV02897.proved (move-product MV00676.proved (MV02897.proved)))))))

module r4b_ij1236 where

  proved : X23 • K1236 ≈ M1 • K1236 • M1 • K1236 • M1
  proved = GL.•-cancelʳ {g = X23 • K1236} {g' = M1 • K1236 • M1 • K1236 • M1} {h = p (s0 • s1 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02898.proved (MV00677.proved))) (trans (cong refl R098.proved) (move-product MV02899.proved (move-product MV00677.proved (move-product MV02899.proved (move-product MV00677.proved (MV02899.proved)))))))

module r4b_ij1237 where

  proved : X23 • K1237 ≈ M1 • K1237 • M1 • K1237 • M1
  proved = GL.•-cancelʳ {g = X23 • K1237} {g' = M1 • K1237 • M1 • K1237 • M1} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02900.proved (MV00678.proved))) (trans (cong refl R098.proved) (move-product MV02901.proved (move-product MV00678.proved (move-product MV02901.proved (move-product MV00678.proved (MV02901.proved)))))))

module r4b_ij1245 where

  proved : X24 • K1245 ≈ M1 • K1245 • M1 • K1245 • M1
  proved = GL.•-cancelʳ {g = X24 • K1245} {g' = M1 • K1245 • M1 • K1245 • M1} {h = p (s0 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV02902.proved (MV00679.proved))) (trans (cong refl R098.proved) (move-product MV02903.proved (move-product MV00679.proved (move-product MV02903.proved (move-product MV00679.proved (MV02903.proved)))))))

module r4b_ij1246 where

  proved : X24 • K1246 ≈ M1 • K1246 • M1 • K1246 • M1
  proved = GL.•-cancelʳ {g = X24 • K1246} {g' = M1 • K1246 • M1 • K1246 • M1} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02904.proved (MV00680.proved))) (trans (cong refl R098.proved) (move-product MV02905.proved (move-product MV00680.proved (move-product MV02905.proved (move-product MV00680.proved (MV02905.proved)))))))

module r4b_ij1247 where

  proved : X24 • K1247 ≈ M1 • K1247 • M1 • K1247 • M1
  proved = GL.•-cancelʳ {g = X24 • K1247} {g' = M1 • K1247 • M1 • K1247 • M1} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02906.proved (MV00681.proved))) (trans (cong refl R098.proved) (move-product MV02907.proved (move-product MV00681.proved (move-product MV02907.proved (move-product MV00681.proved (MV02907.proved)))))))

module r4b_ij1256 where

  proved : X25 • K1256 ≈ M1 • K1256 • M1 • K1256 • M1
  proved = GL.•-cancelʳ {g = X25 • K1256} {g' = M1 • K1256 • M1 • K1256 • M1} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02908.proved (MV00682.proved))) (trans (cong refl R098.proved) (move-product MV02909.proved (move-product MV00682.proved (move-product MV02909.proved (move-product MV00682.proved (MV02909.proved)))))))

module r4b_ij1257 where

  proved : X25 • K1257 ≈ M1 • K1257 • M1 • K1257 • M1
  proved = GL.•-cancelʳ {g = X25 • K1257} {g' = M1 • K1257 • M1 • K1257 • M1} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02910.proved (MV00683.proved))) (trans (cong refl R098.proved) (move-product MV02911.proved (move-product MV00683.proved (move-product MV02911.proved (move-product MV00683.proved (MV02911.proved)))))))

module r4b_ij1267 where

  proved : X26 • K1267 ≈ M1 • K1267 • M1 • K1267 • M1
  proved = GL.•-cancelʳ {g = X26 • K1267} {g' = M1 • K1267 • M1 • K1267 • M1} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02912.proved (MV00684.proved))) (trans (cong refl R098.proved) (move-product MV02913.proved (move-product MV00684.proved (move-product MV02913.proved (move-product MV00684.proved (MV02913.proved)))))))

module r4b_ij1345 where

  proved : X34 • K1345 ≈ M1 • K1345 • M1 • K1345 • M1
  proved = GL.•-cancelʳ {g = X34 • K1345} {g' = M1 • K1345 • M1 • K1345 • M1} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV02914.proved (MV00685.proved))) (trans (cong refl R098.proved) (move-product MV02915.proved (move-product MV00685.proved (move-product MV02915.proved (move-product MV00685.proved (MV02915.proved)))))))

module r4b_ij1346 where

  proved : X34 • K1346 ≈ M1 • K1346 • M1 • K1346 • M1
  proved = GL.•-cancelʳ {g = X34 • K1346} {g' = M1 • K1346 • M1 • K1346 • M1} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02916.proved (MV00686.proved))) (trans (cong refl R098.proved) (move-product MV02917.proved (move-product MV00686.proved (move-product MV02917.proved (move-product MV00686.proved (MV02917.proved)))))))

module r4b_ij1347 where

  proved : X34 • K1347 ≈ M1 • K1347 • M1 • K1347 • M1
  proved = GL.•-cancelʳ {g = X34 • K1347} {g' = M1 • K1347 • M1 • K1347 • M1} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02918.proved (MV00687.proved))) (trans (cong refl R098.proved) (move-product MV02919.proved (move-product MV00687.proved (move-product MV02919.proved (move-product MV00687.proved (MV02919.proved)))))))

module r4b_ij1356 where

  proved : X35 • K1356 ≈ M1 • K1356 • M1 • K1356 • M1
  proved = GL.•-cancelʳ {g = X35 • K1356} {g' = M1 • K1356 • M1 • K1356 • M1} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02920.proved (MV00688.proved))) (trans (cong refl R098.proved) (move-product MV02921.proved (move-product MV00688.proved (move-product MV02921.proved (move-product MV00688.proved (MV02921.proved)))))))

module r4b_ij1357 where

  proved : X35 • K1357 ≈ M1 • K1357 • M1 • K1357 • M1
  proved = GL.•-cancelʳ {g = X35 • K1357} {g' = M1 • K1357 • M1 • K1357 • M1} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02922.proved (MV00689.proved))) (trans (cong refl R098.proved) (move-product MV02923.proved (move-product MV00689.proved (move-product MV02923.proved (move-product MV00689.proved (MV02923.proved)))))))
