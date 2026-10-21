{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; NK ; X05 ; X06 ; X07 ; X13 ; X14 ; X15 ; X16 ; X17 ; X23 ; X24 ; X25 ; X26 ; X27 ; X34 ; X35 ; X36 ; X37 ; X45 ; X46 ; X47 ; X56 ; X57 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameCommutations.B000 using (module CM00013)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B000 using (module PE00147 ; module PE00155 ; module PE00163)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00005)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B002 using (module PE00084 ; module PE00085 ; module PE00086 ; module PE00087 ; module PE00088 ; module PE00089 ; module PE00090 ; module PE00091 ; module PE00092 ; module PE00093 ; module PE00094 ; module PE00095 ; module PE00096 ; module PE00097 ; module PE00098 ; module PE00099 ; module PE00100 ; module PE00101 ; module PE00102 ; module PE00103 ; module PE00104 ; module PE00105 ; module PE00106 ; module PE00107 ; module PE00108 ; module PE00109 ; module PE00110 ; module PE00111)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B003 using (module PE00112 ; module PE00113 ; module PE00114 ; module PE00115 ; module PE00116 ; module PE00117 ; module PE00118 ; module PE00119 ; module PE00120 ; module PE00121 ; module PE00122 ; module PE00123 ; module PE00124 ; module PE00125 ; module PE00126 ; module PE00127 ; module PE00128 ; module PE00129 ; module PE00130 ; module PE00131 ; module PE00132 ; module PE00133 ; module PE00134 ; module PE00135 ; module PE00136 ; module PE00137 ; module PE00138 ; module PE00139 ; module PE00140 ; module PE00141 ; module PE00142 ; module PE00143 ; module PE00144 ; module PE00145 ; module PE00146 ; module PE00148 ; module PE00149 ; module PE00150 ; module PE00151 ; module PE00152 ; module PE00153 ; module PE00154 ; module PE00156 ; module PE00157 ; module PE00158 ; module PE00159 ; module PE00160 ; module PE00161 ; module PE00162 ; module PE00164 ; module PE00165 ; module PE00166 ; module PE00167 ; module PE00168 ; module PE00169 ; module PE00170 ; module PE00171 ; module PE00172 ; module PE00173 ; module PE00174 ; module PE00175 ; module PE00176 ; module PE00177)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B004 using (module PE00178 ; module PE00179 ; module PE00180 ; module PE00181 ; module PE00182 ; module PE00183 ; module PE00184 ; module PE00185 ; module PE00186 ; module PE00187 ; module PE00188 ; module PE00189 ; module PE00190 ; module PE00191 ; module PE00192 ; module PE00193 ; module PE00194 ; module PE00195 ; module PE00196 ; module PE00197 ; module PE00198 ; module PE00199 ; module PE00200 ; module PE00201 ; module PE00202 ; module PE00203 ; module PE00204 ; module PE00205 ; module PE00206 ; module PE00207 ; module PE00208 ; module PE00209)

module MV00119 where

  proved : p (s2) • X14 ≈ X14 • p (s2)
  proved = by-assoc-and PE00084.proved Eq.refl Eq.refl

module MV00120 where

  proved : p (s3) • X14 ≈ X13 • p (s3)
  proved = by-assoc-and PE00085.proved Eq.refl Eq.refl

module MV00121 where

  proved : p (s4) • X14 ≈ X15 • p (s4)
  proved = by-assoc-and PE00086.proved Eq.refl Eq.refl

module MV00122 where

  proved : p (s5) • X14 ≈ X14 • p (s5)
  proved = by-assoc-and PE00087.proved Eq.refl Eq.refl

module MV00123 where

  proved : p (s6) • X14 ≈ X14 • p (s6)
  proved = by-assoc-and PE00088.proved Eq.refl Eq.refl

module MV00124 where

  proved : p (s0) • X15 ≈ X05 • p (s0)
  proved = by-assoc-and PE00089.proved Eq.refl Eq.refl

module MV00125 where

  proved : p (s1) • X15 ≈ X25 • p (s1)
  proved = by-assoc-and PE00090.proved Eq.refl Eq.refl

module MV00126 where

  proved : p (s2) • X15 ≈ X15 • p (s2)
  proved = by-assoc-and PE00091.proved Eq.refl Eq.refl

module MV00127 where

  proved : p (s3) • X15 ≈ X15 • p (s3)
  proved = by-assoc-and PE00092.proved Eq.refl Eq.refl

module MV00128 where

  proved : p (s4) • X15 ≈ X14 • p (s4)
  proved = by-assoc-and PE00093.proved Eq.refl Eq.refl

module MV00129 where

  proved : p (s5) • X15 ≈ X16 • p (s5)
  proved = by-assoc-and PE00094.proved Eq.refl Eq.refl

module MV00130 where

  proved : p (s6) • X15 ≈ X15 • p (s6)
  proved = by-assoc-and PE00095.proved Eq.refl Eq.refl

module MV00131 where

  proved : p (s0) • X16 ≈ X06 • p (s0)
  proved = by-assoc-and PE00096.proved Eq.refl Eq.refl

module MV00132 where

  proved : p (s1) • X16 ≈ X26 • p (s1)
  proved = by-assoc-and PE00097.proved Eq.refl Eq.refl

module MV00133 where

  proved : p (s2) • X16 ≈ X16 • p (s2)
  proved = by-assoc-and PE00098.proved Eq.refl Eq.refl

module MV00134 where

  proved : p (s3) • X16 ≈ X16 • p (s3)
  proved = by-assoc-and PE00099.proved Eq.refl Eq.refl

module MV00135 where

  proved : p (s4) • X16 ≈ X16 • p (s4)
  proved = by-assoc-and PE00100.proved Eq.refl Eq.refl

module MV00136 where

  proved : p (s5) • X16 ≈ X15 • p (s5)
  proved = by-assoc-and PE00101.proved Eq.refl Eq.refl

module MV00137 where

  proved : p (s6) • X16 ≈ X17 • p (s6)
  proved = by-assoc-and PE00102.proved Eq.refl Eq.refl

module MV00138 where

  proved : p (s0) • X17 ≈ X07 • p (s0)
  proved = by-assoc-and PE00103.proved Eq.refl Eq.refl

module MV00139 where

  proved : p (s1) • X17 ≈ X27 • p (s1)
  proved = by-assoc-and PE00104.proved Eq.refl Eq.refl

module MV00140 where

  proved : p (s2) • X17 ≈ X17 • p (s2)
  proved = by-assoc-and PE00105.proved Eq.refl Eq.refl

module MV00141 where

  proved : p (s3) • X17 ≈ X17 • p (s3)
  proved = by-assoc-and PE00106.proved Eq.refl Eq.refl

module MV00142 where

  proved : p (s4) • X17 ≈ X17 • p (s4)
  proved = by-assoc-and PE00107.proved Eq.refl Eq.refl

module MV00143 where

  proved : p (s5) • X17 ≈ X17 • p (s5)
  proved = by-assoc-and PE00108.proved Eq.refl Eq.refl

module MV00144 where

  proved : p (s6) • X17 ≈ X16 • p (s6)
  proved = by-assoc-and PE00109.proved Eq.refl Eq.refl

module MV00145 where

  proved : p (s0) • X23 ≈ X23 • p (s0)
  proved = by-assoc-and PE00110.proved Eq.refl Eq.refl

module MV00146 where

  proved : p (s1) • X23 ≈ X13 • p (s1)
  proved = by-assoc-and PE00111.proved Eq.refl Eq.refl

module MV00147 where

  proved : p (s3) • X23 ≈ X24 • p (s3)
  proved = by-assoc-and PE00112.proved Eq.refl Eq.refl

module MV00148 where

  proved : p (s4) • X23 ≈ X23 • p (s4)
  proved = by-assoc-and PE00113.proved Eq.refl Eq.refl

module MV00149 where

  proved : p (s5) • X23 ≈ X23 • p (s5)
  proved = by-assoc-and PE00114.proved Eq.refl Eq.refl

module MV00150 where

  proved : p (s6) • X23 ≈ X23 • p (s6)
  proved = by-assoc-and PE00115.proved Eq.refl Eq.refl

module MV00151 where

  proved : p (s0) • X24 ≈ X24 • p (s0)
  proved = by-assoc-and PE00116.proved Eq.refl Eq.refl

module MV00152 where

  proved : p (s1) • X24 ≈ X14 • p (s1)
  proved = by-assoc-and PE00117.proved Eq.refl Eq.refl

module MV00153 where

  proved : p (s2) • X24 ≈ X34 • p (s2)
  proved = by-assoc-and PE00118.proved Eq.refl Eq.refl

module MV00154 where

  proved : p (s3) • X24 ≈ X23 • p (s3)
  proved = by-assoc-and PE00119.proved Eq.refl Eq.refl

module MV00155 where

  proved : p (s4) • X24 ≈ X25 • p (s4)
  proved = by-assoc-and PE00120.proved Eq.refl Eq.refl

module MV00156 where

  proved : p (s5) • X24 ≈ X24 • p (s5)
  proved = by-assoc-and PE00121.proved Eq.refl Eq.refl

module MV00157 where

  proved : p (s6) • X24 ≈ X24 • p (s6)
  proved = by-assoc-and PE00122.proved Eq.refl Eq.refl

module MV00158 where

  proved : p (s0) • X25 ≈ X25 • p (s0)
  proved = by-assoc-and PE00123.proved Eq.refl Eq.refl

module MV00159 where

  proved : p (s1) • X25 ≈ X15 • p (s1)
  proved = by-assoc-and PE00124.proved Eq.refl Eq.refl

module MV00160 where

  proved : p (s2) • X25 ≈ X35 • p (s2)
  proved = by-assoc-and PE00125.proved Eq.refl Eq.refl

module MV00161 where

  proved : p (s3) • X25 ≈ X25 • p (s3)
  proved = by-assoc-and PE00126.proved Eq.refl Eq.refl

module MV00162 where

  proved : p (s4) • X25 ≈ X24 • p (s4)
  proved = by-assoc-and PE00127.proved Eq.refl Eq.refl

module MV00163 where

  proved : p (s5) • X25 ≈ X26 • p (s5)
  proved = by-assoc-and PE00128.proved Eq.refl Eq.refl

module MV00164 where

  proved : p (s6) • X25 ≈ X25 • p (s6)
  proved = by-assoc-and PE00129.proved Eq.refl Eq.refl

module MV00165 where

  proved : p (s0) • X26 ≈ X26 • p (s0)
  proved = by-assoc-and PE00130.proved Eq.refl Eq.refl

module MV00166 where

  proved : p (s1) • X26 ≈ X16 • p (s1)
  proved = by-assoc-and PE00131.proved Eq.refl Eq.refl

module MV00167 where

  proved : p (s2) • X26 ≈ X36 • p (s2)
  proved = by-assoc-and PE00132.proved Eq.refl Eq.refl

module MV00168 where

  proved : p (s3) • X26 ≈ X26 • p (s3)
  proved = by-assoc-and PE00133.proved Eq.refl Eq.refl

module MV00169 where

  proved : p (s4) • X26 ≈ X26 • p (s4)
  proved = by-assoc-and PE00134.proved Eq.refl Eq.refl

module MV00170 where

  proved : p (s5) • X26 ≈ X25 • p (s5)
  proved = by-assoc-and PE00135.proved Eq.refl Eq.refl

module MV00171 where

  proved : p (s6) • X26 ≈ X27 • p (s6)
  proved = by-assoc-and PE00136.proved Eq.refl Eq.refl

module MV00172 where

  proved : p (s0) • X27 ≈ X27 • p (s0)
  proved = by-assoc-and PE00137.proved Eq.refl Eq.refl

module MV00173 where

  proved : p (s1) • X27 ≈ X17 • p (s1)
  proved = by-assoc-and PE00138.proved Eq.refl Eq.refl

module MV00174 where

  proved : p (s2) • X27 ≈ X37 • p (s2)
  proved = by-assoc-and PE00139.proved Eq.refl Eq.refl

module MV00175 where

  proved : p (s3) • X27 ≈ X27 • p (s3)
  proved = by-assoc-and PE00140.proved Eq.refl Eq.refl

module MV00176 where

  proved : p (s4) • X27 ≈ X27 • p (s4)
  proved = by-assoc-and PE00141.proved Eq.refl Eq.refl

module MV00177 where

  proved : p (s5) • X27 ≈ X27 • p (s5)
  proved = by-assoc-and PE00142.proved Eq.refl Eq.refl

module MV00178 where

  proved : p (s6) • X27 ≈ X26 • p (s6)
  proved = by-assoc-and PE00143.proved Eq.refl Eq.refl

module MV00179 where

  proved : p (s0) • X34 ≈ X34 • p (s0)
  proved = by-assoc-and PE00144.proved Eq.refl Eq.refl

module MV00180 where

  proved : p (s1) • X34 ≈ X34 • p (s1)
  proved = by-assoc-and PE00145.proved Eq.refl Eq.refl

module MV00181 where

  proved : p (s2) • X34 ≈ X24 • p (s2)
  proved = by-assoc-and PE00146.proved Eq.refl Eq.refl

module MV00182 where

  proved : p (s4) • X34 ≈ X35 • p (s4)
  proved = by-assoc-and PE00147.proved Eq.refl Eq.refl

module MV00183 where

  proved : p (s5) • X34 ≈ X34 • p (s5)
  proved = by-assoc-and PE00148.proved Eq.refl Eq.refl

module MV00184 where

  proved : p (s6) • X34 ≈ X34 • p (s6)
  proved = by-assoc-and PE00149.proved Eq.refl Eq.refl

module MV00185 where

  proved : p (s0) • X35 ≈ X35 • p (s0)
  proved = by-assoc-and PE00150.proved Eq.refl Eq.refl

module MV00186 where

  proved : p (s1) • X35 ≈ X35 • p (s1)
  proved = by-assoc-and PE00151.proved Eq.refl Eq.refl

module MV00187 where

  proved : p (s2) • X35 ≈ X25 • p (s2)
  proved = by-assoc-and PE00152.proved Eq.refl Eq.refl

module MV00188 where

  proved : p (s3) • X35 ≈ X45 • p (s3)
  proved = by-assoc-and PE00153.proved Eq.refl Eq.refl

module MV00189 where

  proved : p (s4) • X35 ≈ X34 • p (s4)
  proved = by-assoc-and PE00154.proved Eq.refl Eq.refl

module MV00190 where

  proved : p (s5) • X35 ≈ X36 • p (s5)
  proved = by-assoc-and PE00155.proved Eq.refl Eq.refl

module MV00191 where

  proved : p (s6) • X35 ≈ X35 • p (s6)
  proved = by-assoc-and PE00156.proved Eq.refl Eq.refl

module MV00192 where

  proved : p (s0) • X36 ≈ X36 • p (s0)
  proved = by-assoc-and PE00157.proved Eq.refl Eq.refl

module MV00193 where

  proved : p (s1) • X36 ≈ X36 • p (s1)
  proved = by-assoc-and PE00158.proved Eq.refl Eq.refl

module MV00194 where

  proved : p (s2) • X36 ≈ X26 • p (s2)
  proved = by-assoc-and PE00159.proved Eq.refl Eq.refl

module MV00195 where

  proved : p (s3) • X36 ≈ X46 • p (s3)
  proved = by-assoc-and PE00160.proved Eq.refl Eq.refl

module MV00196 where

  proved : p (s4) • X36 ≈ X36 • p (s4)
  proved = by-assoc-and PE00161.proved Eq.refl Eq.refl

module MV00197 where

  proved : p (s5) • X36 ≈ X35 • p (s5)
  proved = by-assoc-and PE00162.proved Eq.refl Eq.refl

module MV00198 where

  proved : p (s6) • X36 ≈ X37 • p (s6)
  proved = by-assoc-and PE00163.proved Eq.refl Eq.refl

module MV00199 where

  proved : p (s0) • X37 ≈ X37 • p (s0)
  proved = by-assoc-and PE00164.proved Eq.refl Eq.refl

module MV00200 where

  proved : p (s1) • X37 ≈ X37 • p (s1)
  proved = by-assoc-and PE00165.proved Eq.refl Eq.refl

module MV00201 where

  proved : p (s2) • X37 ≈ X27 • p (s2)
  proved = by-assoc-and PE00166.proved Eq.refl Eq.refl

module MV00202 where

  proved : p (s3) • X37 ≈ X47 • p (s3)
  proved = by-assoc-and PE00167.proved Eq.refl Eq.refl

module MV00203 where

  proved : p (s4) • X37 ≈ X37 • p (s4)
  proved = by-assoc-and PE00168.proved Eq.refl Eq.refl

module MV00204 where

  proved : p (s5) • X37 ≈ X37 • p (s5)
  proved = by-assoc-and PE00169.proved Eq.refl Eq.refl

module MV00205 where

  proved : p (s6) • X37 ≈ X36 • p (s6)
  proved = by-assoc-and PE00170.proved Eq.refl Eq.refl

module MV00206 where

  proved : p (s0) • X45 ≈ X45 • p (s0)
  proved = by-assoc-and PE00171.proved Eq.refl Eq.refl

module MV00207 where

  proved : p (s1) • X45 ≈ X45 • p (s1)
  proved = by-assoc-and PE00172.proved Eq.refl Eq.refl

module MV00208 where

  proved : p (s2) • X45 ≈ X45 • p (s2)
  proved = by-assoc-and PE00173.proved Eq.refl Eq.refl

module MV00209 where

  proved : p (s3) • X45 ≈ X35 • p (s3)
  proved = by-assoc-and PE00174.proved Eq.refl Eq.refl

module MV00210 where

  proved : p (s5) • X45 ≈ X46 • p (s5)
  proved = by-assoc-and PE00175.proved Eq.refl Eq.refl

module MV00211 where

  proved : p (s6) • X45 ≈ X45 • p (s6)
  proved = by-assoc-and PE00176.proved Eq.refl Eq.refl

module MV00212 where

  proved : p (s0) • X46 ≈ X46 • p (s0)
  proved = by-assoc-and PE00177.proved Eq.refl Eq.refl

module MV00213 where

  proved : p (s1) • X46 ≈ X46 • p (s1)
  proved = by-assoc-and PE00178.proved Eq.refl Eq.refl

module MV00214 where

  proved : p (s2) • X46 ≈ X46 • p (s2)
  proved = by-assoc-and PE00179.proved Eq.refl Eq.refl

module MV00215 where

  proved : p (s3) • X46 ≈ X36 • p (s3)
  proved = by-assoc-and PE00180.proved Eq.refl Eq.refl

module MV00216 where

  proved : p (s4) • X46 ≈ X56 • p (s4)
  proved = by-assoc-and PE00181.proved Eq.refl Eq.refl

module MV00217 where

  proved : p (s5) • X46 ≈ X45 • p (s5)
  proved = by-assoc-and PE00182.proved Eq.refl Eq.refl

module MV00218 where

  proved : p (s6) • X46 ≈ X47 • p (s6)
  proved = by-assoc-and PE00183.proved Eq.refl Eq.refl

module MV00219 where

  proved : p (s0) • X47 ≈ X47 • p (s0)
  proved = by-assoc-and PE00184.proved Eq.refl Eq.refl

module MV00220 where

  proved : p (s1) • X47 ≈ X47 • p (s1)
  proved = by-assoc-and PE00185.proved Eq.refl Eq.refl

module MV00221 where

  proved : p (s2) • X47 ≈ X47 • p (s2)
  proved = by-assoc-and PE00186.proved Eq.refl Eq.refl

module MV00222 where

  proved : p (s3) • X47 ≈ X37 • p (s3)
  proved = by-assoc-and PE00187.proved Eq.refl Eq.refl

module MV00223 where

  proved : p (s4) • X47 ≈ X57 • p (s4)
  proved = by-assoc-and PE00188.proved Eq.refl Eq.refl

module MV00224 where

  proved : p (s5) • X47 ≈ X47 • p (s5)
  proved = by-assoc-and PE00189.proved Eq.refl Eq.refl

module MV00225 where

  proved : p (s6) • X47 ≈ X46 • p (s6)
  proved = by-assoc-and PE00190.proved Eq.refl Eq.refl

module MV00226 where

  proved : p (s0) • X56 ≈ X56 • p (s0)
  proved = by-assoc-and PE00191.proved Eq.refl Eq.refl

module MV00227 where

  proved : p (s1) • X56 ≈ X56 • p (s1)
  proved = by-assoc-and PE00192.proved Eq.refl Eq.refl

module MV00228 where

  proved : p (s2) • X56 ≈ X56 • p (s2)
  proved = by-assoc-and PE00193.proved Eq.refl Eq.refl

module MV00229 where

  proved : p (s3) • X56 ≈ X56 • p (s3)
  proved = by-assoc-and PE00194.proved Eq.refl Eq.refl

module MV00230 where

  proved : p (s4) • X56 ≈ X46 • p (s4)
  proved = by-assoc-and PE00195.proved Eq.refl Eq.refl

module MV00231 where

  proved : p (s6) • X56 ≈ X57 • p (s6)
  proved = by-assoc-and PE00196.proved Eq.refl Eq.refl

module MV00232 where

  proved : p (s0) • X57 ≈ X57 • p (s0)
  proved = by-assoc-and PE00197.proved Eq.refl Eq.refl

module MV00233 where

  proved : p (s1) • X57 ≈ X57 • p (s1)
  proved = by-assoc-and PE00198.proved Eq.refl Eq.refl

module MV00234 where

  proved : p (s2) • X57 ≈ X57 • p (s2)
  proved = by-assoc-and PE00199.proved Eq.refl Eq.refl

module MV00235 where

  proved : p (s3) • X57 ≈ X57 • p (s3)
  proved = by-assoc-and PE00200.proved Eq.refl Eq.refl

module MV00236 where

  proved : p (s4) • X57 ≈ X47 • p (s4)
  proved = by-assoc-and PE00201.proved Eq.refl Eq.refl

module MV00237 where

  proved : p (s5) • X57 ≈ X67 • p (s5)
  proved = by-assoc-and PE00202.proved Eq.refl Eq.refl

module MV00238 where

  proved : p (s6) • X57 ≈ X56 • p (s6)
  proved = by-assoc-and PE00203.proved Eq.refl Eq.refl

module MV00239 where

  proved : p (s0) • X67 ≈ X67 • p (s0)
  proved = by-assoc-and PE00204.proved Eq.refl Eq.refl

module MV00240 where

  proved : p (s1) • X67 ≈ X67 • p (s1)
  proved = by-assoc-and PE00205.proved Eq.refl Eq.refl

module MV00241 where

  proved : p (s2) • X67 ≈ X67 • p (s2)
  proved = by-assoc-and PE00206.proved Eq.refl Eq.refl

module MV00242 where

  proved : p (s3) • X67 ≈ X67 • p (s3)
  proved = by-assoc-and PE00207.proved Eq.refl Eq.refl

module MV00243 where

  proved : p (s4) • X67 ≈ X67 • p (s4)
  proved = by-assoc-and PE00208.proved Eq.refl Eq.refl

module MV00244 where

  proved : p (s5) • X67 ≈ X57 • p (s5)
  proved = by-assoc-and PE00209.proved Eq.refl Eq.refl

module MV00246 where

  step0 : p (s4) • K0123 ≈ p (ε) • p (s4) • NK • p (ε)
  step0 = by-assoc-and (under (ε) (NK • p (ε)) PE00005.proved) Eq.refl Eq.refl

  step1 : p (ε) • p (s4) • NK • p (ε) ≈ p (ε) • NK • p (s4) • p (ε)
  step1 = by-assoc-and (under (p (ε)) (p (ε)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (ε) • NK • p (s4) • p (ε) ≈ K0123 • p (s4)
  step2 = by-assoc-and (under (p (ε) • NK) (ε) PE00005.proved) Eq.refl Eq.refl

  proved : p (s4) • K0123 ≈ K0123 • p (s4)
  proved = trans step0 (trans step1 step2)
