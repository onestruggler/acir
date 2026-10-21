{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B049 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000 ; module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00001 ; module MV00002 ; module MV00003 ; module MV00004 ; module MV00005 ; module MV00006 ; module MV00007 ; module MV00009 ; module MV00010 ; module MV00011 ; module MV00012 ; module MV00013 ; module MV00014 ; module MV00015 ; module MV00016 ; module MV00017 ; module MV00018 ; module MV00019 ; module MV00020 ; module MV00021 ; module MV00022 ; module MV00023 ; module MV00024 ; module MV00025 ; module MV00026 ; module MV00027 ; module MV00028 ; module MV00029 ; module MV00030 ; module MV00031 ; module MV00032 ; module MV00033 ; module MV00034 ; module MV00035 ; module MV00036 ; module MV00037 ; module MV00038 ; module MV00039 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00041 ; module MV00042 ; module MV00043 ; module MV00044 ; module MV00045 ; module MV00046 ; module MV00047 ; module MV00048 ; module MV00049 ; module MV00050 ; module MV00051 ; module MV00052 ; module MV00053 ; module MV00054 ; module MV00055)

module MV01877 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3) • M4 ≈ M1 • p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3)
  proved = by-assoc-and (move-compose MV00012.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00023.proved (MV00031.proved)))))))) Eq.refl Eq.refl

module MV01878 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s3) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s3)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (MV00003.proved))))))) Eq.refl Eq.refl

module MV01879 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s3) • M4 ≈ M2 • p (s5 • s4 • s3 • s2 • s1 • s0 • s3)
  proved = by-assoc-and (move-compose MV00019.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00021.proved (MV00031.proved))))))) Eq.refl Eq.refl

module MV01880 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0) • M4 ≈ M3 • p (s5 • s4 • s3 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00026.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (MV00028.proved)))))) Eq.refl Eq.refl

module MV01881 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s4) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s4)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (MV00004.proved))))))) Eq.refl Eq.refl

module MV01882 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s4) • M4 ≈ M4 • p (s5 • s4 • s3 • s2 • s1 • s0 • s4)
  proved = by-assoc-and (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00035.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV01883 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00005.proved (MV00004.proved)))))))) Eq.refl Eq.refl

module MV01884 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4) • M4 ≈ M5 • p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4)
  proved = by-assoc-and (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00043.proved (move-compose MV00042.proved (move-compose MV00040.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV01885 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00006.proved (move-compose MV00005.proved (MV00004.proved))))))))) Eq.refl Eq.refl

module MV01886 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4) • M4 ≈ M7 • p (s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00049.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV01887 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00002.proved (MV00003.proved)))))))))) Eq.refl Eq.refl

module MV01888 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3) • M4 ≈ M0 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00023.proved (MV00031.proved)))))))))) Eq.refl Eq.refl

module MV01889 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (MV00003.proved))))))))) Eq.refl Eq.refl

module MV01890 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3) • M4 ≈ M1 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3)
  proved = by-assoc-and (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00023.proved (MV00031.proved))))))))) Eq.refl Eq.refl

module MV01891 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (MV00003.proved)))))))) Eq.refl Eq.refl

module MV01892 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3) • M4 ≈ M2 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3)
  proved = by-assoc-and (move-compose MV00020.proved (move-compose MV00019.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00021.proved (MV00031.proved)))))))) Eq.refl Eq.refl

module MV01893 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0) • M4 ≈ M3 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (MV00028.proved))))))) Eq.refl Eq.refl

module MV01894 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (MV00004.proved)))))))) Eq.refl Eq.refl

module MV01895 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4) • M4 ≈ M4 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4)
  proved = by-assoc-and (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00035.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV01896 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00005.proved (MV00004.proved))))))))) Eq.refl Eq.refl

module MV01897 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4) • M4 ≈ M5 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4)
  proved = by-assoc-and (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00043.proved (move-compose MV00042.proved (move-compose MV00040.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV01898 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00006.proved (move-compose MV00005.proved (MV00004.proved)))))))))) Eq.refl Eq.refl

module MV01899 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4) • M4 ≈ M6 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00049.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV01900 where

  proved : p (s0 • s1 • s2 • s4 • s3) • M4 ≈ M0 • p (s0 • s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00023.proved (move-compose MV00025.proved (MV00031.proved))))) Eq.refl Eq.refl

module MV01901 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3) • M4 ≈ M0 • p (s0 • s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))) Eq.refl Eq.refl

module MV01902 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))) Eq.refl Eq.refl

module MV01903 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3) • M4 ≈ M0 • p (s0 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00025.proved (MV00031.proved)))))) Eq.refl Eq.refl

module MV01904 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3) • M4 ≈ M0 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))) Eq.refl Eq.refl

module MV01905 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))) Eq.refl Eq.refl

module MV01906 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M4 ≈ M0 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))) Eq.refl Eq.refl

module MV01907 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))))) Eq.refl Eq.refl

module MV01908 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00019.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))))) Eq.refl Eq.refl

module MV01909 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3) • M4 ≈ M0 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00025.proved (MV00031.proved))))))) Eq.refl Eq.refl

module MV01910 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • M4 ≈ M0 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))) Eq.refl Eq.refl

module MV01911 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))))) Eq.refl Eq.refl

module MV01912 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M4 ≈ M0 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))))) Eq.refl Eq.refl

module MV01913 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))))) Eq.refl Eq.refl

module MV01914 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00019.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))))))) Eq.refl Eq.refl

module MV01915 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M4 ≈ M0 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))))) Eq.refl Eq.refl

module MV01916 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))))))) Eq.refl Eq.refl

module MV01917 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00019.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))))))) Eq.refl Eq.refl

module MV01918 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00019.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))))))))) Eq.refl Eq.refl
