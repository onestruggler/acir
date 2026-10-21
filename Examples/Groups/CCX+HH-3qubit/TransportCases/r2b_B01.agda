{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_B01 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; X15 ; X16 ; X17 ; X23 ; X24 ; X25 ; X26 ; X27 ; X34 ; X35 ; X36 ; X37 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B020 using (module MV00826 ; module MV00827)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B021 using (module MV00828 ; module MV00829 ; module MV00830 ; module MV00831 ; module MV00832 ; module MV00833 ; module MV00834 ; module MV00835 ; module MV00836 ; module MV00837 ; module MV00838 ; module MV00839 ; module MV00840 ; module MV00841 ; module MV00842 ; module MV00843 ; module MV00844 ; module MV00845 ; module MV00846 ; module MV00847 ; module MV00848 ; module MV00849 ; module MV00850 ; module MV00851 ; module MV00852 ; module MV00853 ; module MV00854 ; module MV00855 ; module MV00856 ; module MV00857 ; module MV00858 ; module MV00859 ; module MV00860 ; module MV00861 ; module MV00862 ; module MV00863 ; module MV00864 ; module MV00865 ; module MV00866 ; module MV00867 ; module MV00868 ; module MV00869 ; module MV00870 ; module MV00871)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B022 using (module MV00872 ; module MV00873 ; module MV00874 ; module MV00875 ; module MV00876 ; module MV00877 ; module MV00878 ; module MV00879 ; module MV00880 ; module MV00881 ; module MV00882 ; module MV00883 ; module MV00884 ; module MV00885 ; module MV00886 ; module MV00887 ; module MV00888 ; module MV00889 ; module MV00890 ; module MV00891 ; module MV00892 ; module MV00893 ; module MV00894 ; module MV00895 ; module MV00896 ; module MV00897 ; module MV00898 ; module MV00899 ; module MV00900 ; module MV00901 ; module MV00902 ; module MV00903 ; module MV00904 ; module MV00905 ; module MV00906 ; module MV00907 ; module MV00908 ; module MV00909 ; module MV00910)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B023 using (module MV00911 ; module MV00912 ; module MV00913 ; module MV00914 ; module MV00915 ; module MV00916 ; module MV00917 ; module MV00918 ; module MV00919 ; module MV00920 ; module MV00921 ; module MV00922 ; module MV00923 ; module MV00924 ; module MV00925 ; module MV00926 ; module MV00927 ; module MV00928 ; module MV00929 ; module MV00930 ; module MV00931 ; module MV00932 ; module MV00933 ; module MV00934 ; module MV00935 ; module MV00936 ; module MV00937 ; module MV00938 ; module MV00939 ; module MV00940 ; module MV00941 ; module MV00942 ; module MV00943 ; module MV00944 ; module MV00945 ; module MV00946 ; module MV00947 ; module MV00948 ; module MV00949)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B024 using (module MV00950 ; module MV00951)
open import Examples.Groups.CCX+HH-3qubit.FrameRelations.B000 using (module R085)

module r2b_ij156 where

  proved : X15 • M6 ≈ M6 • X15
  proved = GL.•-cancelʳ {g = X15 • M6} {g' = M6 • X15} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00826.proved (MV00827.proved))) (trans (cong refl R085.proved) (move-product MV00827.proved (MV00826.proved))))

module r2b_ij157 where

  proved : X15 • M7 ≈ M7 • X15
  proved = GL.•-cancelʳ {g = X15 • M7} {g' = M7 • X15} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00828.proved (MV00829.proved))) (trans (cong refl R085.proved) (move-product MV00829.proved (MV00828.proved))))

module r2b_ij160 where

  proved : X16 • M0 ≈ M0 • X16
  proved = GL.•-cancelʳ {g = X16 • M0} {g' = M0 • X16} {h = p (s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00830.proved (MV00831.proved))) (trans (cong refl R085.proved) (move-product MV00831.proved (MV00830.proved))))

module r2b_ij162 where

  proved : X16 • M2 ≈ M2 • X16
  proved = GL.•-cancelʳ {g = X16 • M2} {g' = M2 • X16} {h = p (s1 • s0 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00832.proved (MV00833.proved))) (trans (cong refl R085.proved) (move-product MV00833.proved (MV00832.proved))))

module r2b_ij163 where

  proved : X16 • M3 ≈ M3 • X16
  proved = GL.•-cancelʳ {g = X16 • M3} {g' = M3 • X16} {h = p (s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00834.proved (MV00835.proved))) (trans (cong refl R085.proved) (move-product MV00835.proved (MV00834.proved))))

module r2b_ij164 where

  proved : X16 • M4 ≈ M4 • X16
  proved = GL.•-cancelʳ {g = X16 • M4} {g' = M4 • X16} {h = p (s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00836.proved (MV00837.proved))) (trans (cong refl R085.proved) (move-product MV00837.proved (MV00836.proved))))

module r2b_ij165 where

  proved : X16 • M5 ≈ M5 • X16
  proved = GL.•-cancelʳ {g = X16 • M5} {g' = M5 • X16} {h = p (s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00838.proved (MV00839.proved))) (trans (cong refl R085.proved) (move-product MV00839.proved (MV00838.proved))))

module r2b_ij167 where

  proved : X16 • M7 ≈ M7 • X16
  proved = GL.•-cancelʳ {g = X16 • M7} {g' = M7 • X16} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00840.proved (MV00841.proved))) (trans (cong refl R085.proved) (move-product MV00841.proved (MV00840.proved))))

module r2b_ij170 where

  proved : X17 • M0 ≈ M0 • X17
  proved = GL.•-cancelʳ {g = X17 • M0} {g' = M0 • X17} {h = p (s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00842.proved (MV00843.proved))) (trans (cong refl R085.proved) (move-product MV00843.proved (MV00842.proved))))

module r2b_ij172 where

  proved : X17 • M2 ≈ M2 • X17
  proved = GL.•-cancelʳ {g = X17 • M2} {g' = M2 • X17} {h = p (s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00844.proved (MV00845.proved))) (trans (cong refl R085.proved) (move-product MV00845.proved (MV00844.proved))))

module r2b_ij173 where

  proved : X17 • M3 ≈ M3 • X17
  proved = GL.•-cancelʳ {g = X17 • M3} {g' = M3 • X17} {h = p (s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00846.proved (MV00847.proved))) (trans (cong refl R085.proved) (move-product MV00847.proved (MV00846.proved))))

module r2b_ij174 where

  proved : X17 • M4 ≈ M4 • X17
  proved = GL.•-cancelʳ {g = X17 • M4} {g' = M4 • X17} {h = p (s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00848.proved (MV00849.proved))) (trans (cong refl R085.proved) (move-product MV00849.proved (MV00848.proved))))

module r2b_ij175 where

  proved : X17 • M5 ≈ M5 • X17
  proved = GL.•-cancelʳ {g = X17 • M5} {g' = M5 • X17} {h = p (s4 • s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00850.proved (MV00851.proved))) (trans (cong refl R085.proved) (move-product MV00851.proved (MV00850.proved))))

module r2b_ij176 where

  proved : X17 • M6 ≈ M6 • X17
  proved = GL.•-cancelʳ {g = X17 • M6} {g' = M6 • X17} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00852.proved (MV00853.proved))) (trans (cong refl R085.proved) (move-product MV00853.proved (MV00852.proved))))

module r2b_ij230 where

  proved : X23 • M0 ≈ M0 • X23
  proved = GL.•-cancelʳ {g = X23 • M0} {g' = M0 • X23} {h = p (s1 • s2)}
    (trans (sym (move-product MV00854.proved (MV00855.proved))) (trans (cong refl R085.proved) (move-product MV00855.proved (MV00854.proved))))

module r2b_ij231 where

  proved : X23 • M1 ≈ M1 • X23
  proved = GL.•-cancelʳ {g = X23 • M1} {g' = M1 • X23} {h = p (s0 • s1 • s2)}
    (trans (sym (move-product MV00856.proved (MV00857.proved))) (trans (cong refl R085.proved) (move-product MV00857.proved (MV00856.proved))))

module r2b_ij234 where

  proved : X23 • M4 ≈ M4 • X23
  proved = GL.•-cancelʳ {g = X23 • M4} {g' = M4 • X23} {h = p (s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2)}
    (trans (sym (move-product MV00858.proved (MV00859.proved))) (trans (cong refl R085.proved) (move-product MV00859.proved (MV00858.proved))))

module r2b_ij235 where

  proved : X23 • M5 ≈ M5 • X23
  proved = GL.•-cancelʳ {g = X23 • M5} {g' = M5 • X23} {h = p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2)}
    (trans (sym (move-product MV00860.proved (MV00861.proved))) (trans (cong refl R085.proved) (move-product MV00861.proved (MV00860.proved))))

module r2b_ij236 where

  proved : X23 • M6 ≈ M6 • X23
  proved = GL.•-cancelʳ {g = X23 • M6} {g' = M6 • X23} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2)}
    (trans (sym (move-product MV00862.proved (MV00863.proved))) (trans (cong refl R085.proved) (move-product MV00863.proved (MV00862.proved))))

module r2b_ij237 where

  proved : X23 • M7 ≈ M7 • X23
  proved = GL.•-cancelʳ {g = X23 • M7} {g' = M7 • X23} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2)}
    (trans (sym (move-product MV00864.proved (MV00865.proved))) (trans (cong refl R085.proved) (move-product MV00865.proved (MV00864.proved))))

module r2b_ij240 where

  proved : X24 • M0 ≈ M0 • X24
  proved = GL.•-cancelʳ {g = X24 • M0} {g' = M0 • X24} {h = p (s1 • s3 • s2)}
    (trans (sym (move-product MV00866.proved (MV00867.proved))) (trans (cong refl R085.proved) (move-product MV00867.proved (MV00866.proved))))

module r2b_ij241 where

  proved : X24 • M1 ≈ M1 • X24
  proved = GL.•-cancelʳ {g = X24 • M1} {g' = M1 • X24} {h = p (s0 • s1 • s3 • s2)}
    (trans (sym (move-product MV00868.proved (MV00869.proved))) (trans (cong refl R085.proved) (move-product MV00869.proved (MV00868.proved))))

module r2b_ij243 where

  proved : X24 • M3 ≈ M3 • X24
  proved = GL.•-cancelʳ {g = X24 • M3} {g' = M3 • X24} {h = p (s2 • s1 • s0 • s2 • s1 • s3 • s2)}
    (trans (sym (move-product MV00870.proved (MV00871.proved))) (trans (cong refl R085.proved) (move-product MV00871.proved (MV00870.proved))))

module r2b_ij245 where

  proved : X24 • M5 ≈ M5 • X24
  proved = GL.•-cancelʳ {g = X24 • M5} {g' = M5 • X24} {h = p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00872.proved (MV00873.proved))) (trans (cong refl R085.proved) (move-product MV00873.proved (MV00872.proved))))

module r2b_ij246 where

  proved : X24 • M6 ≈ M6 • X24
  proved = GL.•-cancelʳ {g = X24 • M6} {g' = M6 • X24} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00874.proved (MV00875.proved))) (trans (cong refl R085.proved) (move-product MV00875.proved (MV00874.proved))))

module r2b_ij247 where

  proved : X24 • M7 ≈ M7 • X24
  proved = GL.•-cancelʳ {g = X24 • M7} {g' = M7 • X24} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00876.proved (MV00877.proved))) (trans (cong refl R085.proved) (move-product MV00877.proved (MV00876.proved))))

module r2b_ij250 where

  proved : X25 • M0 ≈ M0 • X25
  proved = GL.•-cancelʳ {g = X25 • M0} {g' = M0 • X25} {h = p (s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00878.proved (MV00879.proved))) (trans (cong refl R085.proved) (move-product MV00879.proved (MV00878.proved))))

module r2b_ij251 where

  proved : X25 • M1 ≈ M1 • X25
  proved = GL.•-cancelʳ {g = X25 • M1} {g' = M1 • X25} {h = p (s0 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00880.proved (MV00881.proved))) (trans (cong refl R085.proved) (move-product MV00881.proved (MV00880.proved))))

module r2b_ij253 where

  proved : X25 • M3 ≈ M3 • X25
  proved = GL.•-cancelʳ {g = X25 • M3} {g' = M3 • X25} {h = p (s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00882.proved (MV00883.proved))) (trans (cong refl R085.proved) (move-product MV00883.proved (MV00882.proved))))

module r2b_ij254 where

  proved : X25 • M4 ≈ M4 • X25
  proved = GL.•-cancelʳ {g = X25 • M4} {g' = M4 • X25} {h = p (s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00884.proved (MV00885.proved))) (trans (cong refl R085.proved) (move-product MV00885.proved (MV00884.proved))))

module r2b_ij256 where

  proved : X25 • M6 ≈ M6 • X25
  proved = GL.•-cancelʳ {g = X25 • M6} {g' = M6 • X25} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00886.proved (MV00887.proved))) (trans (cong refl R085.proved) (move-product MV00887.proved (MV00886.proved))))

module r2b_ij257 where

  proved : X25 • M7 ≈ M7 • X25
  proved = GL.•-cancelʳ {g = X25 • M7} {g' = M7 • X25} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00888.proved (MV00889.proved))) (trans (cong refl R085.proved) (move-product MV00889.proved (MV00888.proved))))

module r2b_ij260 where

  proved : X26 • M0 ≈ M0 • X26
  proved = GL.•-cancelʳ {g = X26 • M0} {g' = M0 • X26} {h = p (s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00890.proved (MV00891.proved))) (trans (cong refl R085.proved) (move-product MV00891.proved (MV00890.proved))))

module r2b_ij261 where

  proved : X26 • M1 ≈ M1 • X26
  proved = GL.•-cancelʳ {g = X26 • M1} {g' = M1 • X26} {h = p (s0 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00892.proved (MV00893.proved))) (trans (cong refl R085.proved) (move-product MV00893.proved (MV00892.proved))))

module r2b_ij263 where

  proved : X26 • M3 ≈ M3 • X26
  proved = GL.•-cancelʳ {g = X26 • M3} {g' = M3 • X26} {h = p (s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00894.proved (MV00895.proved))) (trans (cong refl R085.proved) (move-product MV00895.proved (MV00894.proved))))

module r2b_ij264 where

  proved : X26 • M4 ≈ M4 • X26
  proved = GL.•-cancelʳ {g = X26 • M4} {g' = M4 • X26} {h = p (s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00896.proved (MV00897.proved))) (trans (cong refl R085.proved) (move-product MV00897.proved (MV00896.proved))))

module r2b_ij265 where

  proved : X26 • M5 ≈ M5 • X26
  proved = GL.•-cancelʳ {g = X26 • M5} {g' = M5 • X26} {h = p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00898.proved (MV00899.proved))) (trans (cong refl R085.proved) (move-product MV00899.proved (MV00898.proved))))

module r2b_ij267 where

  proved : X26 • M7 ≈ M7 • X26
  proved = GL.•-cancelʳ {g = X26 • M7} {g' = M7 • X26} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00900.proved (MV00901.proved))) (trans (cong refl R085.proved) (move-product MV00901.proved (MV00900.proved))))

module r2b_ij270 where

  proved : X27 • M0 ≈ M0 • X27
  proved = GL.•-cancelʳ {g = X27 • M0} {g' = M0 • X27} {h = p (s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00902.proved (MV00903.proved))) (trans (cong refl R085.proved) (move-product MV00903.proved (MV00902.proved))))

module r2b_ij271 where

  proved : X27 • M1 ≈ M1 • X27
  proved = GL.•-cancelʳ {g = X27 • M1} {g' = M1 • X27} {h = p (s0 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00904.proved (MV00905.proved))) (trans (cong refl R085.proved) (move-product MV00905.proved (MV00904.proved))))

module r2b_ij273 where

  proved : X27 • M3 ≈ M3 • X27
  proved = GL.•-cancelʳ {g = X27 • M3} {g' = M3 • X27} {h = p (s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00906.proved (MV00907.proved))) (trans (cong refl R085.proved) (move-product MV00907.proved (MV00906.proved))))

module r2b_ij274 where

  proved : X27 • M4 ≈ M4 • X27
  proved = GL.•-cancelʳ {g = X27 • M4} {g' = M4 • X27} {h = p (s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00908.proved (MV00909.proved))) (trans (cong refl R085.proved) (move-product MV00909.proved (MV00908.proved))))

module r2b_ij275 where

  proved : X27 • M5 ≈ M5 • X27
  proved = GL.•-cancelʳ {g = X27 • M5} {g' = M5 • X27} {h = p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00910.proved (MV00911.proved))) (trans (cong refl R085.proved) (move-product MV00911.proved (MV00910.proved))))

module r2b_ij276 where

  proved : X27 • M6 ≈ M6 • X27
  proved = GL.•-cancelʳ {g = X27 • M6} {g' = M6 • X27} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00912.proved (MV00913.proved))) (trans (cong refl R085.proved) (move-product MV00913.proved (MV00912.proved))))

module r2b_ij340 where

  proved : X34 • M0 ≈ M0 • X34
  proved = GL.•-cancelʳ {g = X34 • M0} {g' = M0 • X34} {h = p (s2 • s1 • s3 • s2)}
    (trans (sym (move-product MV00914.proved (MV00915.proved))) (trans (cong refl R085.proved) (move-product MV00915.proved (MV00914.proved))))

module r2b_ij341 where

  proved : X34 • M1 ≈ M1 • X34
  proved = GL.•-cancelʳ {g = X34 • M1} {g' = M1 • X34} {h = p (s0 • s2 • s1 • s3 • s2)}
    (trans (sym (move-product MV00916.proved (MV00917.proved))) (trans (cong refl R085.proved) (move-product MV00917.proved (MV00916.proved))))

module r2b_ij342 where

  proved : X34 • M2 ≈ M2 • X34
  proved = GL.•-cancelʳ {g = X34 • M2} {g' = M2 • X34} {h = p (s1 • s0 • s2 • s1 • s3 • s2)}
    (trans (sym (move-product MV00918.proved (MV00919.proved))) (trans (cong refl R085.proved) (move-product MV00919.proved (MV00918.proved))))

module r2b_ij345 where

  proved : X34 • M5 ≈ M5 • X34
  proved = GL.•-cancelʳ {g = X34 • M5} {g' = M5 • X34} {h = p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00920.proved (MV00921.proved))) (trans (cong refl R085.proved) (move-product MV00921.proved (MV00920.proved))))

module r2b_ij346 where

  proved : X34 • M6 ≈ M6 • X34
  proved = GL.•-cancelʳ {g = X34 • M6} {g' = M6 • X34} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00922.proved (MV00923.proved))) (trans (cong refl R085.proved) (move-product MV00923.proved (MV00922.proved))))

module r2b_ij347 where

  proved : X34 • M7 ≈ M7 • X34
  proved = GL.•-cancelʳ {g = X34 • M7} {g' = M7 • X34} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00924.proved (MV00925.proved))) (trans (cong refl R085.proved) (move-product MV00925.proved (MV00924.proved))))

module r2b_ij350 where

  proved : X35 • M0 ≈ M0 • X35
  proved = GL.•-cancelʳ {g = X35 • M0} {g' = M0 • X35} {h = p (s2 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00926.proved (MV00927.proved))) (trans (cong refl R085.proved) (move-product MV00927.proved (MV00926.proved))))

module r2b_ij351 where

  proved : X35 • M1 ≈ M1 • X35
  proved = GL.•-cancelʳ {g = X35 • M1} {g' = M1 • X35} {h = p (s0 • s2 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00928.proved (MV00929.proved))) (trans (cong refl R085.proved) (move-product MV00929.proved (MV00928.proved))))

module r2b_ij352 where

  proved : X35 • M2 ≈ M2 • X35
  proved = GL.•-cancelʳ {g = X35 • M2} {g' = M2 • X35} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00930.proved (MV00931.proved))) (trans (cong refl R085.proved) (move-product MV00931.proved (MV00930.proved))))

module r2b_ij354 where

  proved : X35 • M4 ≈ M4 • X35
  proved = GL.•-cancelʳ {g = X35 • M4} {g' = M4 • X35} {h = p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00932.proved (MV00933.proved))) (trans (cong refl R085.proved) (move-product MV00933.proved (MV00932.proved))))

module r2b_ij356 where

  proved : X35 • M6 ≈ M6 • X35
  proved = GL.•-cancelʳ {g = X35 • M6} {g' = M6 • X35} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00934.proved (MV00935.proved))) (trans (cong refl R085.proved) (move-product MV00935.proved (MV00934.proved))))

module r2b_ij357 where

  proved : X35 • M7 ≈ M7 • X35
  proved = GL.•-cancelʳ {g = X35 • M7} {g' = M7 • X35} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00936.proved (MV00937.proved))) (trans (cong refl R085.proved) (move-product MV00937.proved (MV00936.proved))))

module r2b_ij360 where

  proved : X36 • M0 ≈ M0 • X36
  proved = GL.•-cancelʳ {g = X36 • M0} {g' = M0 • X36} {h = p (s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00938.proved (MV00939.proved))) (trans (cong refl R085.proved) (move-product MV00939.proved (MV00938.proved))))

module r2b_ij361 where

  proved : X36 • M1 ≈ M1 • X36
  proved = GL.•-cancelʳ {g = X36 • M1} {g' = M1 • X36} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00940.proved (MV00941.proved))) (trans (cong refl R085.proved) (move-product MV00941.proved (MV00940.proved))))

module r2b_ij362 where

  proved : X36 • M2 ≈ M2 • X36
  proved = GL.•-cancelʳ {g = X36 • M2} {g' = M2 • X36} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00942.proved (MV00943.proved))) (trans (cong refl R085.proved) (move-product MV00943.proved (MV00942.proved))))

module r2b_ij364 where

  proved : X36 • M4 ≈ M4 • X36
  proved = GL.•-cancelʳ {g = X36 • M4} {g' = M4 • X36} {h = p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00944.proved (MV00945.proved))) (trans (cong refl R085.proved) (move-product MV00945.proved (MV00944.proved))))

module r2b_ij365 where

  proved : X36 • M5 ≈ M5 • X36
  proved = GL.•-cancelʳ {g = X36 • M5} {g' = M5 • X36} {h = p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00946.proved (MV00947.proved))) (trans (cong refl R085.proved) (move-product MV00947.proved (MV00946.proved))))

module r2b_ij367 where

  proved : X36 • M7 ≈ M7 • X36
  proved = GL.•-cancelʳ {g = X36 • M7} {g' = M7 • X36} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00948.proved (MV00949.proved))) (trans (cong refl R085.proved) (move-product MV00949.proved (MV00948.proved))))

module r2b_ij370 where

  proved : X37 • M0 ≈ M0 • X37
  proved = GL.•-cancelʳ {g = X37 • M0} {g' = M0 • X37} {h = p (s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00950.proved (MV00951.proved))) (trans (cong refl R085.proved) (move-product MV00951.proved (MV00950.proved))))
