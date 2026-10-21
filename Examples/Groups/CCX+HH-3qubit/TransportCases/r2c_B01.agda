{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_B01 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1234 ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1267 ; K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; K1367 ; K1456 ; K1457 ; K1467 ; K2345 ; K2346 ; K2347 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K3456 ; K3457 ; K3467 ; K3567 ; K4567 ; X05 ; X06 ; X07 ; X12 ; X13 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B017 using (module MV00659 ; module MV00665 ; module MV00666 ; module MV00667 ; module MV00668 ; module MV00669 ; module MV00670 ; module MV00671 ; module MV00672 ; module MV00673 ; module MV00674 ; module MV00675)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B029 using (module MV01120 ; module MV01121 ; module MV01122 ; module MV01123 ; module MV01124 ; module MV01125 ; module MV01126 ; module MV01127 ; module MV01128 ; module MV01129 ; module MV01130 ; module MV01131 ; module MV01132 ; module MV01133 ; module MV01134 ; module MV01135 ; module MV01136 ; module MV01137 ; module MV01138 ; module MV01139 ; module MV01140 ; module MV01141 ; module MV01142 ; module MV01143 ; module MV01144 ; module MV01145 ; module MV01146 ; module MV01147 ; module MV01148)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B030 using (module MV01149 ; module MV01150 ; module MV01151 ; module MV01152 ; module MV01153 ; module MV01154 ; module MV01155 ; module MV01156 ; module MV01157 ; module MV01158 ; module MV01159 ; module MV01160 ; module MV01161 ; module MV01162 ; module MV01163 ; module MV01164 ; module MV01165 ; module MV01166 ; module MV01167 ; module MV01168 ; module MV01169 ; module MV01170 ; module MV01171 ; module MV01172 ; module MV01173 ; module MV01174 ; module MV01175 ; module MV01176 ; module MV01177 ; module MV01178 ; module MV01179 ; module MV01180 ; module MV01181 ; module MV01182 ; module MV01183 ; module MV01184 ; module MV01185)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B031 using (module MV01186 ; module MV01187 ; module MV01188 ; module MV01189 ; module MV01190 ; module MV01191 ; module MV01192 ; module MV01193 ; module MV01194 ; module MV01195 ; module MV01196 ; module MV01197 ; module MV01198 ; module MV01199 ; module MV01200 ; module MV01201 ; module MV01202 ; module MV01203 ; module MV01204 ; module MV01205 ; module MV01206 ; module MV01207 ; module MV01208 ; module MV01209 ; module MV01210 ; module MV01211 ; module MV01212 ; module MV01213 ; module MV01214 ; module MV01215 ; module MV01216 ; module MV01217 ; module MV01218 ; module MV01219 ; module MV01220)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B032 using (module MV01221 ; module MV01222 ; module MV01223 ; module MV01224 ; module MV01225 ; module MV01226 ; module MV01227 ; module MV01228 ; module MV01229)
open import Examples.Groups.CCX+HH-3qubit.FrameRelations.B000 using (module R091)

module r2c_ij051234 where

  proved : X05 • K1234 ≈ K1234 • X05
  proved = GL.•-cancelʳ {g = X05 • K1234} {g' = K1234 • X05} {h = p (s0 • s1 • s2 • s3)}
    (trans (sym (move-product MV01120.proved (MV00675.proved))) (trans (cong refl R091.proved) (move-product MV00675.proved (MV01120.proved))))

module r2c_ij051236 where

  proved : X05 • K1236 ≈ K1236 • X05
  proved = GL.•-cancelʳ {g = X05 • K1236} {g' = K1236 • X05} {h = p (s0 • s1 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01121.proved (MV01122.proved))) (trans (cong refl R091.proved) (move-product MV01122.proved (MV01121.proved))))

module r2c_ij051237 where

  proved : X05 • K1237 ≈ K1237 • X05
  proved = GL.•-cancelʳ {g = X05 • K1237} {g' = K1237 • X05} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01123.proved (MV01124.proved))) (trans (cong refl R091.proved) (move-product MV01124.proved (MV01123.proved))))

module r2c_ij051246 where

  proved : X05 • K1246 ≈ K1246 • X05
  proved = GL.•-cancelʳ {g = X05 • K1246} {g' = K1246 • X05} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01125.proved (MV01126.proved))) (trans (cong refl R091.proved) (move-product MV01126.proved (MV01125.proved))))

module r2c_ij051247 where

  proved : X05 • K1247 ≈ K1247 • X05
  proved = GL.•-cancelʳ {g = X05 • K1247} {g' = K1247 • X05} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01127.proved (MV01128.proved))) (trans (cong refl R091.proved) (move-product MV01128.proved (MV01127.proved))))

module r2c_ij051267 where

  proved : X05 • K1267 ≈ K1267 • X05
  proved = GL.•-cancelʳ {g = X05 • K1267} {g' = K1267 • X05} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01129.proved (MV01130.proved))) (trans (cong refl R091.proved) (move-product MV01130.proved (MV01129.proved))))

module r2c_ij051346 where

  proved : X05 • K1346 ≈ K1346 • X05
  proved = GL.•-cancelʳ {g = X05 • K1346} {g' = K1346 • X05} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01131.proved (MV01132.proved))) (trans (cong refl R091.proved) (move-product MV01132.proved (MV01131.proved))))

module r2c_ij051347 where

  proved : X05 • K1347 ≈ K1347 • X05
  proved = GL.•-cancelʳ {g = X05 • K1347} {g' = K1347 • X05} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01133.proved (MV01134.proved))) (trans (cong refl R091.proved) (move-product MV01134.proved (MV01133.proved))))

module r2c_ij051367 where

  proved : X05 • K1367 ≈ K1367 • X05
  proved = GL.•-cancelʳ {g = X05 • K1367} {g' = K1367 • X05} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01135.proved (MV01136.proved))) (trans (cong refl R091.proved) (move-product MV01136.proved (MV01135.proved))))

module r2c_ij051467 where

  proved : X05 • K1467 ≈ K1467 • X05
  proved = GL.•-cancelʳ {g = X05 • K1467} {g' = K1467 • X05} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01137.proved (MV01138.proved))) (trans (cong refl R091.proved) (move-product MV01138.proved (MV01137.proved))))

module r2c_ij052346 where

  proved : X05 • K2346 ≈ K2346 • X05
  proved = GL.•-cancelʳ {g = X05 • K2346} {g' = K2346 • X05} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01139.proved (MV01140.proved))) (trans (cong refl R091.proved) (move-product MV01140.proved (MV01139.proved))))

module r2c_ij052347 where

  proved : X05 • K2347 ≈ K2347 • X05
  proved = GL.•-cancelʳ {g = X05 • K2347} {g' = K2347 • X05} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01141.proved (MV01142.proved))) (trans (cong refl R091.proved) (move-product MV01142.proved (MV01141.proved))))

module r2c_ij052367 where

  proved : X05 • K2367 ≈ K2367 • X05
  proved = GL.•-cancelʳ {g = X05 • K2367} {g' = K2367 • X05} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01143.proved (MV01144.proved))) (trans (cong refl R091.proved) (move-product MV01144.proved (MV01143.proved))))

module r2c_ij052467 where

  proved : X05 • K2467 ≈ K2467 • X05
  proved = GL.•-cancelʳ {g = X05 • K2467} {g' = K2467 • X05} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01145.proved (MV01146.proved))) (trans (cong refl R091.proved) (move-product MV01146.proved (MV01145.proved))))

module r2c_ij053467 where

  proved : X05 • K3467 ≈ K3467 • X05
  proved = GL.•-cancelʳ {g = X05 • K3467} {g' = K3467 • X05} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01147.proved (MV01148.proved))) (trans (cong refl R091.proved) (move-product MV01148.proved (MV01147.proved))))

module r2c_ij061234 where

  proved : X06 • K1234 ≈ K1234 • X06
  proved = GL.•-cancelʳ {g = X06 • K1234} {g' = K1234 • X06} {h = p (s0 • s1 • s2 • s3 • s5)}
    (trans (sym (move-product MV01149.proved (MV01150.proved))) (trans (cong refl R091.proved) (move-product MV01150.proved (MV01149.proved))))

module r2c_ij061235 where

  proved : X06 • K1235 ≈ K1235 • X06
  proved = GL.•-cancelʳ {g = X06 • K1235} {g' = K1235 • X06} {h = p (s0 • s1 • s2 • s4 • s3 • s5)}
    (trans (sym (move-product MV01151.proved (MV01152.proved))) (trans (cong refl R091.proved) (move-product MV01152.proved (MV01151.proved))))

module r2c_ij061237 where

  proved : X06 • K1237 ≈ K1237 • X06
  proved = GL.•-cancelʳ {g = X06 • K1237} {g' = K1237 • X06} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01153.proved (MV01154.proved))) (trans (cong refl R091.proved) (move-product MV01154.proved (MV01153.proved))))

module r2c_ij061245 where

  proved : X06 • K1245 ≈ K1245 • X06
  proved = GL.•-cancelʳ {g = X06 • K1245} {g' = K1245 • X06} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s5)}
    (trans (sym (move-product MV01155.proved (MV01156.proved))) (trans (cong refl R091.proved) (move-product MV01156.proved (MV01155.proved))))

module r2c_ij061247 where

  proved : X06 • K1247 ≈ K1247 • X06
  proved = GL.•-cancelʳ {g = X06 • K1247} {g' = K1247 • X06} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01157.proved (MV01158.proved))) (trans (cong refl R091.proved) (move-product MV01158.proved (MV01157.proved))))

module r2c_ij061257 where

  proved : X06 • K1257 ≈ K1257 • X06
  proved = GL.•-cancelʳ {g = X06 • K1257} {g' = K1257 • X06} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01159.proved (MV01160.proved))) (trans (cong refl R091.proved) (move-product MV01160.proved (MV01159.proved))))

module r2c_ij061345 where

  proved : X06 • K1345 ≈ K1345 • X06
  proved = GL.•-cancelʳ {g = X06 • K1345} {g' = K1345 • X06} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5)}
    (trans (sym (move-product MV01161.proved (MV01162.proved))) (trans (cong refl R091.proved) (move-product MV01162.proved (MV01161.proved))))

module r2c_ij061347 where

  proved : X06 • K1347 ≈ K1347 • X06
  proved = GL.•-cancelʳ {g = X06 • K1347} {g' = K1347 • X06} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01163.proved (MV01164.proved))) (trans (cong refl R091.proved) (move-product MV01164.proved (MV01163.proved))))

module r2c_ij061357 where

  proved : X06 • K1357 ≈ K1357 • X06
  proved = GL.•-cancelʳ {g = X06 • K1357} {g' = K1357 • X06} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01165.proved (MV01166.proved))) (trans (cong refl R091.proved) (move-product MV01166.proved (MV01165.proved))))

module r2c_ij061457 where

  proved : X06 • K1457 ≈ K1457 • X06
  proved = GL.•-cancelʳ {g = X06 • K1457} {g' = K1457 • X06} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01167.proved (MV01168.proved))) (trans (cong refl R091.proved) (move-product MV01168.proved (MV01167.proved))))

module r2c_ij062345 where

  proved : X06 • K2345 ≈ K2345 • X06
  proved = GL.•-cancelʳ {g = X06 • K2345} {g' = K2345 • X06} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5)}
    (trans (sym (move-product MV01169.proved (MV01170.proved))) (trans (cong refl R091.proved) (move-product MV01170.proved (MV01169.proved))))

module r2c_ij062347 where

  proved : X06 • K2347 ≈ K2347 • X06
  proved = GL.•-cancelʳ {g = X06 • K2347} {g' = K2347 • X06} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01171.proved (MV01172.proved))) (trans (cong refl R091.proved) (move-product MV01172.proved (MV01171.proved))))

module r2c_ij062357 where

  proved : X06 • K2357 ≈ K2357 • X06
  proved = GL.•-cancelʳ {g = X06 • K2357} {g' = K2357 • X06} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01173.proved (MV01174.proved))) (trans (cong refl R091.proved) (move-product MV01174.proved (MV01173.proved))))

module r2c_ij062457 where

  proved : X06 • K2457 ≈ K2457 • X06
  proved = GL.•-cancelʳ {g = X06 • K2457} {g' = K2457 • X06} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01175.proved (MV01176.proved))) (trans (cong refl R091.proved) (move-product MV01176.proved (MV01175.proved))))

module r2c_ij063457 where

  proved : X06 • K3457 ≈ K3457 • X06
  proved = GL.•-cancelʳ {g = X06 • K3457} {g' = K3457 • X06} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01177.proved (MV01178.proved))) (trans (cong refl R091.proved) (move-product MV01178.proved (MV01177.proved))))

module r2c_ij071234 where

  proved : X07 • K1234 ≈ K1234 • X07
  proved = GL.•-cancelʳ {g = X07 • K1234} {g' = K1234 • X07} {h = p (s0 • s1 • s2 • s3 • s6 • s5)}
    (trans (sym (move-product MV01179.proved (MV01180.proved))) (trans (cong refl R091.proved) (move-product MV01180.proved (MV01179.proved))))

module r2c_ij071235 where

  proved : X07 • K1235 ≈ K1235 • X07
  proved = GL.•-cancelʳ {g = X07 • K1235} {g' = K1235 • X07} {h = p (s0 • s1 • s2 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01181.proved (MV01182.proved))) (trans (cong refl R091.proved) (move-product MV01182.proved (MV01181.proved))))

module r2c_ij071236 where

  proved : X07 • K1236 ≈ K1236 • X07
  proved = GL.•-cancelʳ {g = X07 • K1236} {g' = K1236 • X07} {h = p (s0 • s1 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01183.proved (MV01184.proved))) (trans (cong refl R091.proved) (move-product MV01184.proved (MV01183.proved))))

module r2c_ij071245 where

  proved : X07 • K1245 ≈ K1245 • X07
  proved = GL.•-cancelʳ {g = X07 • K1245} {g' = K1245 • X07} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01185.proved (MV01186.proved))) (trans (cong refl R091.proved) (move-product MV01186.proved (MV01185.proved))))

module r2c_ij071246 where

  proved : X07 • K1246 ≈ K1246 • X07
  proved = GL.•-cancelʳ {g = X07 • K1246} {g' = K1246 • X07} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01187.proved (MV01188.proved))) (trans (cong refl R091.proved) (move-product MV01188.proved (MV01187.proved))))

module r2c_ij071256 where

  proved : X07 • K1256 ≈ K1256 • X07
  proved = GL.•-cancelʳ {g = X07 • K1256} {g' = K1256 • X07} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01189.proved (MV01190.proved))) (trans (cong refl R091.proved) (move-product MV01190.proved (MV01189.proved))))

module r2c_ij071345 where

  proved : X07 • K1345 ≈ K1345 • X07
  proved = GL.•-cancelʳ {g = X07 • K1345} {g' = K1345 • X07} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01191.proved (MV01192.proved))) (trans (cong refl R091.proved) (move-product MV01192.proved (MV01191.proved))))

module r2c_ij071346 where

  proved : X07 • K1346 ≈ K1346 • X07
  proved = GL.•-cancelʳ {g = X07 • K1346} {g' = K1346 • X07} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01193.proved (MV01194.proved))) (trans (cong refl R091.proved) (move-product MV01194.proved (MV01193.proved))))

module r2c_ij071356 where

  proved : X07 • K1356 ≈ K1356 • X07
  proved = GL.•-cancelʳ {g = X07 • K1356} {g' = K1356 • X07} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01195.proved (MV01196.proved))) (trans (cong refl R091.proved) (move-product MV01196.proved (MV01195.proved))))

module r2c_ij071456 where

  proved : X07 • K1456 ≈ K1456 • X07
  proved = GL.•-cancelʳ {g = X07 • K1456} {g' = K1456 • X07} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01197.proved (MV01198.proved))) (trans (cong refl R091.proved) (move-product MV01198.proved (MV01197.proved))))

module r2c_ij072345 where

  proved : X07 • K2345 ≈ K2345 • X07
  proved = GL.•-cancelʳ {g = X07 • K2345} {g' = K2345 • X07} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01199.proved (MV01200.proved))) (trans (cong refl R091.proved) (move-product MV01200.proved (MV01199.proved))))

module r2c_ij072346 where

  proved : X07 • K2346 ≈ K2346 • X07
  proved = GL.•-cancelʳ {g = X07 • K2346} {g' = K2346 • X07} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01201.proved (MV01202.proved))) (trans (cong refl R091.proved) (move-product MV01202.proved (MV01201.proved))))

module r2c_ij072356 where

  proved : X07 • K2356 ≈ K2356 • X07
  proved = GL.•-cancelʳ {g = X07 • K2356} {g' = K2356 • X07} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01203.proved (MV01204.proved))) (trans (cong refl R091.proved) (move-product MV01204.proved (MV01203.proved))))

module r2c_ij072456 where

  proved : X07 • K2456 ≈ K2456 • X07
  proved = GL.•-cancelʳ {g = X07 • K2456} {g' = K2456 • X07} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01205.proved (MV01206.proved))) (trans (cong refl R091.proved) (move-product MV01206.proved (MV01205.proved))))

module r2c_ij073456 where

  proved : X07 • K3456 ≈ K3456 • X07
  proved = GL.•-cancelʳ {g = X07 • K3456} {g' = K3456 • X07} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01207.proved (MV01208.proved))) (trans (cong refl R091.proved) (move-product MV01208.proved (MV01207.proved))))

module r2c_ij120345 where

  proved : X12 • K0345 ≈ K0345 • X12
  proved = GL.•-cancelʳ {g = X12 • K0345} {g' = K0345 • X12} {h = p (s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV01209.proved (MV00665.proved))) (trans (cong refl R091.proved) (move-product MV00665.proved (MV01209.proved))))

module r2c_ij120346 where

  proved : X12 • K0346 ≈ K0346 • X12
  proved = GL.•-cancelʳ {g = X12 • K0346} {g' = K0346 • X12} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01210.proved (MV00666.proved))) (trans (cong refl R091.proved) (move-product MV00666.proved (MV01210.proved))))

module r2c_ij120347 where

  proved : X12 • K0347 ≈ K0347 • X12
  proved = GL.•-cancelʳ {g = X12 • K0347} {g' = K0347 • X12} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01211.proved (MV00667.proved))) (trans (cong refl R091.proved) (move-product MV00667.proved (MV01211.proved))))

module r2c_ij120356 where

  proved : X12 • K0356 ≈ K0356 • X12
  proved = GL.•-cancelʳ {g = X12 • K0356} {g' = K0356 • X12} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01212.proved (MV00668.proved))) (trans (cong refl R091.proved) (move-product MV00668.proved (MV01212.proved))))

module r2c_ij120357 where

  proved : X12 • K0357 ≈ K0357 • X12
  proved = GL.•-cancelʳ {g = X12 • K0357} {g' = K0357 • X12} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01213.proved (MV00669.proved))) (trans (cong refl R091.proved) (move-product MV00669.proved (MV01213.proved))))

module r2c_ij120367 where

  proved : X12 • K0367 ≈ K0367 • X12
  proved = GL.•-cancelʳ {g = X12 • K0367} {g' = K0367 • X12} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01214.proved (MV00670.proved))) (trans (cong refl R091.proved) (move-product MV00670.proved (MV01214.proved))))

module r2c_ij120456 where

  proved : X12 • K0456 ≈ K0456 • X12
  proved = GL.•-cancelʳ {g = X12 • K0456} {g' = K0456 • X12} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01215.proved (MV00671.proved))) (trans (cong refl R091.proved) (move-product MV00671.proved (MV01215.proved))))

module r2c_ij120457 where

  proved : X12 • K0457 ≈ K0457 • X12
  proved = GL.•-cancelʳ {g = X12 • K0457} {g' = K0457 • X12} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01216.proved (MV00672.proved))) (trans (cong refl R091.proved) (move-product MV00672.proved (MV01216.proved))))

module r2c_ij120467 where

  proved : X12 • K0467 ≈ K0467 • X12
  proved = GL.•-cancelʳ {g = X12 • K0467} {g' = K0467 • X12} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01217.proved (MV00673.proved))) (trans (cong refl R091.proved) (move-product MV00673.proved (MV01217.proved))))

module r2c_ij120567 where

  proved : X12 • K0567 ≈ K0567 • X12
  proved = GL.•-cancelʳ {g = X12 • K0567} {g' = K0567 • X12} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01218.proved (MV00674.proved))) (trans (cong refl R091.proved) (move-product MV00674.proved (MV01218.proved))))

module r2c_ij123456 where

  proved : X12 • K3456 ≈ K3456 • X12
  proved = GL.•-cancelʳ {g = X12 • K3456} {g' = K3456 • X12} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01219.proved (MV01220.proved))) (trans (cong refl R091.proved) (move-product MV01220.proved (MV01219.proved))))

module r2c_ij123457 where

  proved : X12 • K3457 ≈ K3457 • X12
  proved = GL.•-cancelʳ {g = X12 • K3457} {g' = K3457 • X12} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01221.proved (MV01222.proved))) (trans (cong refl R091.proved) (move-product MV01222.proved (MV01221.proved))))

module r2c_ij123467 where

  proved : X12 • K3467 ≈ K3467 • X12
  proved = GL.•-cancelʳ {g = X12 • K3467} {g' = K3467 • X12} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01223.proved (MV01224.proved))) (trans (cong refl R091.proved) (move-product MV01224.proved (MV01223.proved))))

module r2c_ij123567 where

  proved : X12 • K3567 ≈ K3567 • X12
  proved = GL.•-cancelʳ {g = X12 • K3567} {g' = K3567 • X12} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01225.proved (MV01226.proved))) (trans (cong refl R091.proved) (move-product MV01226.proved (MV01225.proved))))

module r2c_ij124567 where

  proved : X12 • K4567 ≈ K4567 • X12
  proved = GL.•-cancelʳ {g = X12 • K4567} {g' = K4567 • X12} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01227.proved (MV01228.proved))) (trans (cong refl R091.proved) (move-product MV01228.proved (MV01227.proved))))

module r2c_ij130245 where

  proved : X13 • K0245 ≈ K0245 • X13
  proved = GL.•-cancelʳ {g = X13 • K0245} {g' = K0245 • X13} {h = p (s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV01229.proved (MV00659.proved))) (trans (cong refl R091.proved) (move-product MV00659.proved (MV01229.proved))))
