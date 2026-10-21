{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B073 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; X12 ; X23 ; X24 ; X25 ; X26 ; X34 ; X35 ; X36 ; X45 ; X46 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00001 ; module MV00002 ; module MV00003 ; module MV00004 ; module MV00005 ; module MV00006)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00105 ; module MV00106 ; module MV00107 ; module MV00108 ; module MV00109 ; module MV00111 ; module MV00113 ; module MV00118)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00121 ; module MV00125 ; module MV00129 ; module MV00132 ; module MV00145 ; module MV00151 ; module MV00153 ; module MV00158 ; module MV00160 ; module MV00165 ; module MV00167 ; module MV00179 ; module MV00188 ; module MV00195 ; module MV00216)

module MV02877 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3) • X12 ≈ X34 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00153.proved (move-compose MV00118.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))) Eq.refl Eq.refl

module MV02878 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3) • M0 ≈ M0 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))) Eq.refl Eq.refl

module MV02879 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X34 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00153.proved (move-compose MV00118.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))) Eq.refl Eq.refl

module MV02880 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M0 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))) Eq.refl Eq.refl

module MV02881 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X12 ≈ X35 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))) Eq.refl Eq.refl

module MV02882 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M0 ≈ M0 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))) Eq.refl Eq.refl

module MV02883 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X35 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))))) Eq.refl Eq.refl

module MV02884 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M0 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))))) Eq.refl Eq.refl

module MV02885 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X36 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))))) Eq.refl Eq.refl

module MV02886 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M0 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))))) Eq.refl Eq.refl

module MV02887 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X12 ≈ X45 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))))) Eq.refl Eq.refl

module MV02888 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M0 ≈ M0 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))))) Eq.refl Eq.refl

module MV02889 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X45 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))))) Eq.refl Eq.refl

module MV02890 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M0 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))))) Eq.refl Eq.refl

module MV02891 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X46 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))))))) Eq.refl Eq.refl

module MV02892 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M0 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))))))) Eq.refl Eq.refl

module MV02893 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X56 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))))))) Eq.refl Eq.refl

module MV02894 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M0 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))))))) Eq.refl Eq.refl

module MV02895 where

  proved : p (s0 • s1 • s2 • s3) • X12 ≈ X23 • p (s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00145.proved (move-compose MV00111.proved (move-compose MV00105.proved (MV00106.proved)))) Eq.refl Eq.refl

module MV02896 where

  proved : p (s0 • s1 • s2 • s4 • s3) • X12 ≈ X23 • p (s0 • s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00145.proved (move-compose MV00111.proved (move-compose MV00105.proved (move-compose MV00107.proved (MV00106.proved))))) Eq.refl Eq.refl

module MV02897 where

  proved : p (s0 • s1 • s2 • s4 • s3) • M0 ≈ M1 • p (s0 • s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00002.proved (move-compose MV00004.proved (MV00003.proved))))) Eq.refl Eq.refl

module MV02898 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3) • X12 ≈ X23 • p (s0 • s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00145.proved (move-compose MV00111.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))) Eq.refl Eq.refl

module MV02899 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3) • M0 ≈ M1 • p (s0 • s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))) Eq.refl Eq.refl

module MV02900 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X23 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00145.proved (move-compose MV00111.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))) Eq.refl Eq.refl

module MV02901 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M1 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))) Eq.refl Eq.refl

module MV02902 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3) • X12 ≈ X24 • p (s0 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00151.proved (move-compose MV00118.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00107.proved (MV00106.proved)))))) Eq.refl Eq.refl

module MV02903 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3) • M0 ≈ M1 • p (s0 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00004.proved (MV00003.proved)))))) Eq.refl Eq.refl

module MV02904 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3) • X12 ≈ X24 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00151.proved (move-compose MV00118.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))) Eq.refl Eq.refl

module MV02905 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3) • M0 ≈ M1 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))) Eq.refl Eq.refl

module MV02906 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X24 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00151.proved (move-compose MV00118.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))) Eq.refl Eq.refl

module MV02907 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M1 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))) Eq.refl Eq.refl

module MV02908 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X12 ≈ X25 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00158.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))) Eq.refl Eq.refl

module MV02909 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M0 ≈ M1 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))) Eq.refl Eq.refl

module MV02910 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X25 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00158.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))))) Eq.refl Eq.refl

module MV02911 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M1 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))))) Eq.refl Eq.refl

module MV02912 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X26 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00165.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))))) Eq.refl Eq.refl

module MV02913 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M1 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))))) Eq.refl Eq.refl

module MV02914 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3) • X12 ≈ X34 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00179.proved (move-compose MV00153.proved (move-compose MV00118.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00107.proved (MV00106.proved))))))) Eq.refl Eq.refl

module MV02915 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3) • M0 ≈ M1 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00004.proved (MV00003.proved))))))) Eq.refl Eq.refl

module MV02916 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • X12 ≈ X34 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00179.proved (move-compose MV00153.proved (move-compose MV00118.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))) Eq.refl Eq.refl

module MV02917 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • M0 ≈ M1 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))) Eq.refl Eq.refl

module MV02918 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X34 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00179.proved (move-compose MV00153.proved (move-compose MV00118.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))))) Eq.refl Eq.refl

module MV02919 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M1 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))))) Eq.refl Eq.refl
