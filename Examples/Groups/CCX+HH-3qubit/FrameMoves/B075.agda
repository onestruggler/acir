{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B075 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M3 ; X12 ; X23 ; X25 ; X26 ; X27 ; X34 ; X35 ; X36 ; X37 ; X45 ; X46 ; X47 ; X56 ; X57 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000 ; module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00001 ; module MV00002 ; module MV00003 ; module MV00004 ; module MV00005 ; module MV00006 ; module MV00016)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00105 ; module MV00106 ; module MV00107 ; module MV00108 ; module MV00109 ; module MV00113)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00121 ; module MV00125 ; module MV00129 ; module MV00132 ; module MV00147 ; module MV00153 ; module MV00155 ; module MV00160 ; module MV00163 ; module MV00167 ; module MV00171 ; module MV00174 ; module MV00179 ; module MV00180 ; module MV00185 ; module MV00186 ; module MV00188 ; module MV00193 ; module MV00195 ; module MV00200 ; module MV00202 ; module MV00206 ; module MV00207 ; module MV00208 ; module MV00212 ; module MV00213 ; module MV00214 ; module MV00216 ; module MV00220 ; module MV00221 ; module MV00223 ; module MV00226 ; module MV00227 ; module MV00228 ; module MV00229 ; module MV00233 ; module MV00234 ; module MV00235 ; module MV00237 ; module MV00240 ; module MV00241 ; module MV00242 ; module MV00243)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00003)

module MV02954 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X12 ≈ X45 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00206.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))))))) Eq.refl Eq.refl

module MV02955 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M0 ≈ M3 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))))))) Eq.refl Eq.refl

module MV02956 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X45 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00206.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))))))))) Eq.refl Eq.refl

module MV02957 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M3 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))))))))) Eq.refl Eq.refl

module MV02958 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X46 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00214.proved (move-compose MV00213.proved (move-compose MV00212.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))))))))) Eq.refl Eq.refl

module MV02959 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M3 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))))))))) Eq.refl Eq.refl

module MV02960 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X56 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00228.proved (move-compose MV00227.proved (move-compose MV00226.proved (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))))))))))) Eq.refl Eq.refl

module MV02961 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M3 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))))))))))) Eq.refl Eq.refl

module MV02962 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X56 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00227.proved (move-compose MV00226.proved (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))))))))))) Eq.refl Eq.refl

module MV02963 where

  proved : p (ε) • X23 ≈ X23 • p (ε)
  proved = by-assoc-and PE00003.proved Eq.refl Eq.refl

module MV02964 where

  proved : p (s4 • s3) • X23 ≈ X25 • p (s4 • s3)
  proved = by-assoc-and (move-compose MV00155.proved (MV00147.proved)) Eq.refl Eq.refl

module MV02965 where

  proved : p (s5 • s4 • s3) • X23 ≈ X26 • p (s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))) Eq.refl Eq.refl

module MV02966 where

  proved : p (s6 • s5 • s4 • s3) • X23 ≈ X27 • p (s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))) Eq.refl Eq.refl

module MV02967 where

  proved : p (s2 • s3) • X23 ≈ X34 • p (s2 • s3)
  proved = by-assoc-and (move-compose MV00153.proved (MV00147.proved)) Eq.refl Eq.refl

module MV02968 where

  proved : p (s2 • s4 • s3) • X23 ≈ X35 • p (s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00160.proved (move-compose MV00155.proved (MV00147.proved))) Eq.refl Eq.refl

module MV02969 where

  proved : p (s2 • s5 • s4 • s3) • X23 ≈ X36 • p (s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))) Eq.refl Eq.refl

module MV02970 where

  proved : p (s2 • s6 • s5 • s4 • s3) • X23 ≈ X37 • p (s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))) Eq.refl Eq.refl

module MV02971 where

  proved : p (s3 • s2 • s4 • s3) • X23 ≈ X45 • p (s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00155.proved (MV00147.proved)))) Eq.refl Eq.refl

module MV02972 where

  proved : p (s3 • s2 • s5 • s4 • s3) • X23 ≈ X46 • p (s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))) Eq.refl Eq.refl

module MV02973 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X47 • p (s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))) Eq.refl Eq.refl

module MV02974 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3) • X23 ≈ X56 • p (s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))) Eq.refl Eq.refl

module MV02975 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X57 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))) Eq.refl Eq.refl

module MV02976 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X67 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))) Eq.refl Eq.refl

module MV02977 where

  proved : p (s1 • s2 • s3) • X23 ≈ X34 • p (s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00180.proved (move-compose MV00153.proved (MV00147.proved))) Eq.refl Eq.refl

module MV02978 where

  proved : p (s1 • s2 • s4 • s3) • X23 ≈ X35 • p (s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00186.proved (move-compose MV00160.proved (move-compose MV00155.proved (MV00147.proved)))) Eq.refl Eq.refl

module MV02979 where

  proved : p (s1 • s2 • s5 • s4 • s3) • X23 ≈ X36 • p (s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00193.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))) Eq.refl Eq.refl

module MV02980 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X37 • p (s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00200.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))) Eq.refl Eq.refl

module MV02981 where

  proved : p (s1 • s3 • s2 • s4 • s3) • X23 ≈ X45 • p (s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00207.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00155.proved (MV00147.proved))))) Eq.refl Eq.refl

module MV02982 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3) • X23 ≈ X46 • p (s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00213.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))) Eq.refl Eq.refl

module MV02983 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X47 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00220.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))) Eq.refl Eq.refl

module MV02984 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3) • X23 ≈ X56 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00227.proved (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))) Eq.refl Eq.refl

module MV02985 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X57 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00233.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))) Eq.refl Eq.refl

module MV02986 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X67 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00240.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))))) Eq.refl Eq.refl

module MV02987 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3) • X23 ≈ X45 • p (s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00155.proved (MV00147.proved)))))) Eq.refl Eq.refl

module MV02988 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3) • X23 ≈ X46 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00214.proved (move-compose MV00213.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))) Eq.refl Eq.refl

module MV02989 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X47 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00221.proved (move-compose MV00220.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))) Eq.refl Eq.refl

module MV02990 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X23 ≈ X56 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00228.proved (move-compose MV00227.proved (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))) Eq.refl Eq.refl

module MV02991 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X57 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00234.proved (move-compose MV00233.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))))) Eq.refl Eq.refl

module MV02992 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X67 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))))) Eq.refl Eq.refl

module MV02993 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X23 ≈ X56 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00227.proved (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))))) Eq.refl Eq.refl

module MV02994 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X57 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00233.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))))) Eq.refl Eq.refl

module MV02995 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X67 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))))))) Eq.refl Eq.refl

module MV02996 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X67 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))))))) Eq.refl Eq.refl

module MV02997 where

  proved : p (s0 • s1 • s2 • s3) • X23 ≈ X34 • p (s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00179.proved (move-compose MV00180.proved (move-compose MV00153.proved (MV00147.proved)))) Eq.refl Eq.refl

module MV02998 where

  proved : p (s0 • s1 • s2 • s4 • s3) • X23 ≈ X35 • p (s0 • s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00185.proved (move-compose MV00186.proved (move-compose MV00160.proved (move-compose MV00155.proved (MV00147.proved))))) Eq.refl Eq.refl
