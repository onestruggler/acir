{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD021 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D021 (Sᴰ : SD021) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CS03-CCZ124 : Ws → St 957
  lem-comm-CS03-CCZ124 = pickᴰ 0 Sᴰ
  lem-comm-CS12-CCZ034 : Ws → St 191
  lem-comm-CS12-CCZ034 = pickᴰ 1 Sᴰ
  lem-comm-CS13-CCZ024 : Ws → St 958
  lem-comm-CS13-CCZ024 = pickᴰ 2 Sᴰ
  lem-comm-CS23-CCZ014 : Ws → St 703
  lem-comm-CS23-CCZ014 = pickᴰ 3 Sᴰ
  lem-comm-CS24-CCZ013 : Ws → St 194
  lem-comm-CS24-CCZ013 = pickᴰ 4 Sᴰ
  lem-comm-CSd03-CCZ124 : Ws → St 959
  lem-comm-CSd03-CCZ124 = pickᴰ 5 Sᴰ
  lem-comm-CSd12-CCZ034 : Ws → St 199
  lem-comm-CSd12-CCZ034 = pickᴰ 6 Sᴰ
  lem-comm-CSd13-CCZ024 : Ws → St 960
  lem-comm-CSd13-CCZ024 = pickᴰ 7 Sᴰ
  lem-comm-CSd23-CCZ014 : Ws → St 704
  lem-comm-CSd23-CCZ014 = pickᴰ 8 Sᴰ
  lem-comm-CSd24-CCZ013 : Ws → St 204
  lem-comm-CSd24-CCZ013 = pickᴰ 9 Sᴰ
  lem-comm-CX14-CCZ023 : Ws → St 4
  lem-comm-CX14-CCZ023 = pickᴰ 10 Sᴰ
  lem-comm-CX14-TOFF023 : Ws → St 1056
  lem-comm-CX14-TOFF023 = pickᴰ 11 Sᴰ
  lem-comm-CCZ014-CX23 : Ws → St 893
  lem-comm-CCZ014-CX23 = pickᴰ 12 Sᴰ
  lem-comm-CCZ024-CX13 : Ws → St 1024
  lem-comm-CCZ024-CX13 = pickᴰ 13 Sᴰ
  lem-comm-CS02-CCZ134 : Ws → St 431
  lem-comm-CS02-CCZ134 = pickᴰ 14 Sᴰ
  lem-comm-CSd02-CCZ134 : Ws → St 432
  lem-comm-CSd02-CCZ134 = pickᴰ 15 Sᴰ
  lem-comm-CX31-TOFF024 : Ws → St 1069
  lem-comm-CX31-TOFF024 = pickᴰ 16 Sᴰ
  lem-comm-TOFF013-CX24 : Ws → St 1059
  lem-comm-TOFF013-CX24 = pickᴰ 17 Sᴰ
  lem-comm-TOFF213-CX04 : Ws → St 1028
  lem-comm-TOFF213-CX04 = pickᴰ 18 Sᴰ
  lem-comm-TOFF023-CX14 : Ws → St 1060
  lem-comm-TOFF023-CX14 = pickᴰ 19 Sᴰ
  lem-sym-ab-at0210243143 : Ws → St 53
  lem-sym-ab-at0210243143 = pickᴰ 20 Sᴰ
  lem-sym-ab-at0214203143 : Ws → St 1029
  lem-sym-ab-at0214203143 = pickᴰ 21 Sᴰ
  lem-sym-ab-at03102132 : Ws → St 40
  lem-sym-ab-at03102132 = pickᴰ 22 Sᴰ
  lem-sym-ab-at0314203142 : Ws → St 1031
  lem-sym-ab-at0314203142 = pickᴰ 23 Sᴰ
  lem-sym-ab-at13243142 : Ws → St 895
  lem-sym-ab-at13243142 = pickᴰ 24 Sᴰ
  lem-sym-ab-at14233142 : Ws → St 1070
  lem-sym-ab-at14233142 = pickᴰ 25 Sᴰ
  lem-sym-ab-at243243 : Ws → St 1071
  lem-sym-ab-at243243 = pickᴰ 26 Sᴰ
  lem-sym-ab-at0213243041 : Ws → St 730
  lem-sym-ab-at0213243041 = pickᴰ 27 Sᴰ
  lem-sym-ab-at0214233041 : Ws → St 1072
  lem-sym-ab-at0214233041 = pickᴰ 28 Sᴰ
  lem-sym-ab-at03122031 : Ws → St 1073
  lem-sym-ab-at03122031 = pickᴰ 29 Sᴰ
  lem-sym-ab-at03122130 : Ws → St 1074
  lem-sym-ab-at03122130 = pickᴰ 30 Sᴰ
  lem-sym-ab-at0312243041 : Ws → St 1075
  lem-sym-ab-at0312243041 = pickᴰ 31 Sᴰ
  lem-sym-ab-at0314213240 : Ws → St 1076
  lem-sym-ab-at0314213240 = pickᴰ 32 Sᴰ
  lem-sym-ab-at03143041 : Ws → St 1077
  lem-sym-ab-at03143041 = pickᴰ 33 Sᴰ
  lem-sym-ab-at03243240 : Ws → St 1078
  lem-sym-ab-at03243240 = pickᴰ 34 Sᴰ
  lem-sym-ab-at14213243 : Ws → St 1079
  lem-sym-ab-at14213243 = pickᴰ 35 Sᴰ
  lem-sym-ab-at02132031 : Ws → St 1080
  lem-sym-ab-at02132031 = pickᴰ 36 Sᴰ
  lem-sym-ab-at02132130 : Ws → St 1081
  lem-sym-ab-at02132130 = pickᴰ 37 Sᴰ
  lem-box-tQ-at03102132 : Ws → St 138
  lem-box-tQ-at03102132 = pickᴰ 38 Sᴰ
  lem-box-tQ-at14233241 : Ws → St 88
  lem-box-tQ-at14233241 = pickᴰ 39 Sᴰ
  lem-box-tQ-at0310213442 : Ws → St 149
  lem-box-tQ-at0310213442 = pickᴰ 40 Sᴰ
  lem-box-tQ-at0214203143 : Ws → St 249
  lem-box-tQ-at0214203143 = pickᴰ 41 Sᴰ
  lem-box-tQ-at0310243142 : Ws → St 251
  lem-box-tQ-at0310243142 = pickᴰ 42 Sᴰ
  lem-box-tQ-at0314203142 : Ws → St 310
  lem-box-tQ-at0314203142 = pickᴰ 43 Sᴰ
  lem-box-tQ-at0314213042 : Ws → St 311
  lem-box-tQ-at0314213042 = pickᴰ 44 Sᴰ
  lem-box-tQ-at033440 : Ws → St 340
  lem-box-tQ-at033440 = pickᴰ 45 Sᴰ
  lem-box-tQ-at13213442 : Ws → St 259
  lem-box-tQ-at13213442 = pickᴰ 46 Sᴰ
  lem-box-tQ-at1331 : Ws → St 260
  lem-box-tQ-at1331 = pickᴰ 47 Sᴰ
  lem-box-tQ-at143143 : Ws → St 314
  lem-box-tQ-at143143 = pickᴰ 48 Sᴰ
  lem-box-tQ-at02102441 : Ws → St 348
  lem-box-tQ-at02102441 = pickᴰ 49 Sᴰ
  lem-box-tQ-at02132130 : Ws → St 397
  lem-box-tQ-at02132130 = pickᴰ 50 Sᴰ
  lem-box-tQ-at02142041 : Ws → St 349
  lem-box-tQ-at02142041 = pickᴰ 51 Sᴰ
  lem-box-tQ-at02233440 : Ws → St 330
  lem-box-tQ-at02233440 = pickᴰ 52 Sᴰ
  lem-box-tQ-at0310243241 : Ws → St 350
  lem-box-tQ-at0310243241 = pickᴰ 53 Sᴰ
  lem-box-tQ-at031031 : Ws → St 351
  lem-box-tQ-at031031 = pickᴰ 54 Sᴰ
  lem-box-tQ-at03103441 : Ws → St 352
  lem-box-tQ-at03103441 = pickᴰ 55 Sᴰ
  lem-box-tQ-at03122031 : Ws → St 398
  lem-box-tQ-at03122031 = pickᴰ 56 Sᴰ
  lem-box-tQ-at0312203441 : Ws → St 353
  lem-box-tQ-at0312203441 = pickᴰ 57 Sᴰ
  lem-box-tQ-at03122130 : Ws → St 399
  lem-box-tQ-at03122130 = pickᴰ 58 Sᴰ
  lem-box-tQ-at0314203241 : Ws → St 400
  lem-box-tQ-at0314203241 = pickᴰ 59 Sᴰ
  lem-box-tQ-at0314213240 : Ws → St 355
  lem-box-tQ-at0314213240 = pickᴰ 60 Sᴰ
  lem-box-tQ-at03143140 : Ws → St 357
  lem-box-tQ-at03143140 = pickᴰ 61 Sᴰ
  lem-box-tQ-at03243042 : Ws → St 401
  lem-box-tQ-at03243042 = pickᴰ 62 Sᴰ
  lem-box-tQ-at03243240 : Ws → St 358
  lem-box-tQ-at03243240 = pickᴰ 63 Sᴰ
  lem-box-tQ-at142142 : Ws → St 404
  lem-box-tQ-at142142 = pickᴰ 64 Sᴰ
  lem-P-box-at0214203143 : Ws → St 1082
  lem-P-box-at0214203143 = pickᴰ 65 Sᴰ
  lem-P-box-at02233440 : Ws → St 1083
  lem-P-box-at02233440 = pickᴰ 66 Sᴰ
  lem-P-box-at03103441 : Ws → St 1084
  lem-P-box-at03103441 = pickᴰ 67 Sᴰ
  lem-P-box-at0312203441 : Ws → St 1085
  lem-P-box-at0312203441 = pickᴰ 68 Sᴰ
  lem-P-box-at0314203142 : Ws → St 1086
  lem-P-box-at0314203142 = pickᴰ 69 Sᴰ
  lem-P-box-at0314213042 : Ws → St 1087
  lem-P-box-at0314213042 = pickᴰ 70 Sᴰ
  lem-P-box-at0314213240 : Ws → St 1088
  lem-P-box-at0314213240 = pickᴰ 71 Sᴰ
  lem-P-box-at03243240 : Ws → St 1089
  lem-P-box-at03243240 = pickᴰ 72 Sᴰ
  lem-P-box-at033440 : Ws → St 1090
  lem-P-box-at033440 = pickᴰ 73 Sᴰ
  lem-P-box-at12213443 : Ws → St 1091
  lem-P-box-at12213443 = pickᴰ 74 Sᴰ
  lem-P-box-at1441 : Ws → St 1092
  lem-P-box-at1441 = pickᴰ 75 Sᴰ
  lem-P-box-at233442 : Ws → St 1093
  lem-P-box-at233442 = pickᴰ 76 Sᴰ
  lem-t-cP-at0310243142 : Ws → St 1094
  lem-t-cP-at0310243142 = pickᴰ 77 Sᴰ
  lem-t-cP-at03143140 : Ws → St 1095
  lem-t-cP-at03143140 = pickᴰ 78 Sᴰ
  lem-t-cP-at03243240 : Ws → St 1096
  lem-t-cP-at03243240 = pickᴰ 79 Sᴰ
  lem-P-box-at02102441 : Ws → St 1097
  lem-P-box-at02102441 = pickᴰ 80 Sᴰ
  lem-P-box-at02132130 : Ws → St 1098
  lem-P-box-at02132130 = pickᴰ 81 Sᴰ
  lem-P-box-at0310243241 : Ws → St 1099
  lem-P-box-at0310243241 = pickᴰ 82 Sᴰ
  lem-P-box-at031031 : Ws → St 1100
  lem-P-box-at031031 = pickᴰ 83 Sᴰ
  lem-P-box-at03122130 : Ws → St 1101
  lem-P-box-at03122130 = pickᴰ 84 Sᴰ
  lem-P-box-at0312243041 : Ws → St 1102
  lem-P-box-at0312243041 = pickᴰ 85 Sᴰ
  lem-P-box-at03143041 : Ws → St 1103
  lem-P-box-at03143041 = pickᴰ 86 Sᴰ
  lem-P-box-at03243042 : Ws → St 1104
  lem-P-box-at03243042 = pickᴰ 87 Sᴰ
  lem-P-box-at2442 : Ws → St 1105
  lem-P-box-at2442 = pickᴰ 88 Sᴰ
  lem-t-cP-at02142041 : Ws → St 1106
  lem-t-cP-at02142041 = pickᴰ 89 Sᴰ
  lem-t-cP-at0314203241 : Ws → St 1107
  lem-t-cP-at0314203241 = pickᴰ 90 Sᴰ
  lem-t-cP-at033440 : Ws → St 1108
  lem-t-cP-at033440 = pickᴰ 91 Sᴰ
  lem-t-cP-at142142 : Ws → St 1109
  lem-t-cP-at142142 = pickᴰ 92 Sᴰ
  lem-sym-bc-at0210213443 : Ws → St 956
  lem-sym-bc-at0210213443 = pickᴰ 93 Sᴰ
  lem-sym-bc-at0214233041 : Ws → St 892
  lem-sym-bc-at0214233041 = pickᴰ 94 Sᴰ
  lem-box-cP-at0210243143 : Ws → St 994
  lem-box-cP-at0210243143 = pickᴰ 95 Sᴰ
  lem-box-cP-at02102441 : Ws → St 1110
  lem-box-cP-at02102441 = pickᴰ 96 Sᴰ
  lem-box-cP-at02132130 : Ws → St 1111
  lem-box-cP-at02132130 = pickᴰ 97 Sᴰ
  lem-box-cP-at0214203143 : Ws → St 1112
  lem-box-cP-at0214203143 = pickᴰ 98 Sᴰ
  lem-box-cP-at02233440 : Ws → St 1113
  lem-box-cP-at02233440 = pickᴰ 99 Sᴰ
  lem-box-cP-at022440 : Ws → St 1114
  lem-box-cP-at022440 = pickᴰ 100 Sᴰ
  lem-box-cP-at0310243142 : Ws → St 996
  lem-box-cP-at0310243142 = pickᴰ 101 Sᴰ
  lem-box-cP-at0310243241 : Ws → St 1115
  lem-box-cP-at0310243241 = pickᴰ 102 Sᴰ
  lem-box-cP-at031031 : Ws → St 1116
  lem-box-cP-at031031 = pickᴰ 103 Sᴰ
  lem-box-cP-at03103441 : Ws → St 1117
  lem-box-cP-at03103441 = pickᴰ 104 Sᴰ
  lem-box-cP-at0312203441 : Ws → St 1118
  lem-box-cP-at0312203441 = pickᴰ 105 Sᴰ
  lem-box-cP-at03122130 : Ws → St 1119
  lem-box-cP-at03122130 = pickᴰ 106 Sᴰ
  lem-box-cP-at0312243041 : Ws → St 1120
  lem-box-cP-at0312243041 = pickᴰ 107 Sᴰ
  lem-box-cP-at0314203142 : Ws → St 997
  lem-box-cP-at0314203142 = pickᴰ 108 Sᴰ
  lem-box-cP-at0314213042 : Ws → St 1046
  lem-box-cP-at0314213042 = pickᴰ 109 Sᴰ
  lem-box-cP-at0314213240 : Ws → St 1121
  lem-box-cP-at0314213240 = pickᴰ 110 Sᴰ
  lem-box-cP-at03143041 : Ws → St 1122
  lem-box-cP-at03143041 = pickᴰ 111 Sᴰ
  lem-box-cP-at03143140 : Ws → St 1123
  lem-box-cP-at03143140 = pickᴰ 112 Sᴰ
  lem-box-cP-at03243240 : Ws → St 1124
  lem-box-cP-at03243240 = pickᴰ 113 Sᴰ
  lem-box-cP-at033440 : Ws → St 1125
  lem-box-cP-at033440 = pickᴰ 114 Sᴰ
  lem-box-cP-at12213443 : Ws → St 1126
  lem-box-cP-at12213443 = pickᴰ 115 Sᴰ
  lem-box-cP-at12243143 : Ws → St 1127
  lem-box-cP-at12243143 = pickᴰ 116 Sᴰ
  lem-box-cP-at122441 : Ws → St 1002
  lem-box-cP-at122441 = pickᴰ 117 Sᴰ
  lem-box-cP-at13213442 : Ws → St 1004
  lem-box-cP-at13213442 = pickᴰ 118 Sᴰ
  lem-box-cP-at1441 : Ws → St 1128
  lem-box-cP-at1441 = pickᴰ 119 Sᴰ
  lem-box-cP-at233442 : Ws → St 1129
  lem-box-cP-at233442 = pickᴰ 120 Sᴰ
  lem-box-cP-at243243 : Ws → St 1008
  lem-box-cP-at243243 = pickᴰ 121 Sᴰ
  lem-box-cP-at2442 : Ws → St 1130
  lem-box-cP-at2442 = pickᴰ 122 Sᴰ
  lem-pairs-at021021 : Ws → St 1131
  lem-pairs-at021021 = pickᴰ 123 Sᴰ
  lem-pairs-at0210213443 : Ws → St 1132
  lem-pairs-at0210213443 = pickᴰ 124 Sᴰ
  lem-pairs-at0213243041 : Ws → St 1133
  lem-pairs-at0213243041 = pickᴰ 125 Sᴰ
  lem-pairs-at0214233041 : Ws → St 1134
  lem-pairs-at0214233041 = pickᴰ 126 Sᴰ
  lem-pairs-at03102132 : Ws → St 1135
  lem-pairs-at03102132 = pickᴰ 127 Sᴰ
  lem-pairs-at0310213442 : Ws → St 1136
  lem-pairs-at0310213442 = pickᴰ 128 Sᴰ
  lem-pairs-at13243142 : Ws → St 1010
  lem-pairs-at13243142 = pickᴰ 129 Sᴰ
  lem-pairs-at14233142 : Ws → St 1137
  lem-pairs-at14233142 = pickᴰ 130 Sᴰ
  lem-sym-bc-at0210233441 : Ws → St 1138
  lem-sym-bc-at0210233441 = pickᴰ 131 Sᴰ
  lem-sym-bc-at0210243143 : Ws → St 1014
  lem-sym-bc-at0210243143 = pickᴰ 132 Sᴰ
  lem-sym-bc-at02102441 : Ws → St 1139
  lem-sym-bc-at02102441 = pickᴰ 133 Sᴰ
  lem-sym-bc-at02142041 : Ws → St 1140
  lem-sym-bc-at02142041 = pickᴰ 134 Sᴰ
  lem-sym-bc-at022330 : Ws → St 1141
  lem-sym-bc-at022330 = pickᴰ 135 Sᴰ
  lem-sym-bc-at02233440 : Ws → St 1142
  lem-sym-bc-at02233440 = pickᴰ 136 Sᴰ
  lem-sym-bc-at022440 : Ws → St 1143
  lem-sym-bc-at022440 = pickᴰ 137 Sᴰ
  lem-sym-bc-at0310243142 : Ws → St 1144
  lem-sym-bc-at0310243142 = pickᴰ 138 Sᴰ
  lem-sym-bc-at0310243241 : Ws → St 1145
  lem-sym-bc-at0310243241 = pickᴰ 139 Sᴰ
  lem-sym-bc-at031031 : Ws → St 1146
  lem-sym-bc-at031031 = pickᴰ 140 Sᴰ
  lem-sym-bc-at03103441 : Ws → St 1147
  lem-sym-bc-at03103441 = pickᴰ 141 Sᴰ
  lem-sym-bc-at0312203441 : Ws → St 1148
  lem-sym-bc-at0312203441 = pickᴰ 142 Sᴰ
  lem-sym-bc-at0312243041 : Ws → St 1149
  lem-sym-bc-at0312243041 = pickᴰ 143 Sᴰ
  lem-sym-bc-at0314203241 : Ws → St 1150
  lem-sym-bc-at0314203241 = pickᴰ 144 Sᴰ
  lem-sym-bc-at0314213240 : Ws → St 1151
  lem-sym-bc-at0314213240 = pickᴰ 145 Sᴰ
  lem-sym-bc-at03143041 : Ws → St 1152
  lem-sym-bc-at03143041 = pickᴰ 146 Sᴰ
  lem-sym-bc-at03143140 : Ws → St 1153
  lem-sym-bc-at03143140 = pickᴰ 147 Sᴰ
  lem-sym-bc-at03243240 : Ws → St 1154
  lem-sym-bc-at03243240 = pickᴰ 148 Sᴰ
  lem-sym-bc-at0330 : Ws → St 1015
  lem-sym-bc-at0330 = pickᴰ 149 Sᴰ
  lem-sym-bc-at033440 : Ws → St 1155
  lem-sym-bc-at033440 = pickᴰ 150 Sᴰ
  lem-sym-bc-at12213443 : Ws → St 1156
  lem-sym-bc-at12213443 = pickᴰ 151 Sᴰ
  lem-sym-bc-at12233441 : Ws → St 1157
  lem-sym-bc-at12233441 = pickᴰ 152 Sᴰ
  lem-sym-bc-at12243143 : Ws → St 1158
  lem-sym-bc-at12243143 = pickᴰ 153 Sᴰ
  lem-sym-bc-at13213442 : Ws → St 1019
  lem-sym-bc-at13213442 = pickᴰ 154 Sᴰ
  lem-sym-bc-at14213243 : Ws → St 1159
  lem-sym-bc-at14213243 = pickᴰ 155 Sᴰ
  lem-sym-bc-at143143 : Ws → St 1160
  lem-sym-bc-at143143 = pickᴰ 156 Sᴰ
  lem-sym-bc-at233442 : Ws → St 1161
  lem-sym-bc-at233442 = pickᴰ 157 Sᴰ
  lem-sym-bc-at2442 : Ws → St 1162
  lem-sym-bc-at2442 = pickᴰ 158 Sᴰ
  lem-sym-bc-at3443 : Ws → St 1163
  lem-sym-bc-at3443 = pickᴰ 159 Sᴰ
  lem-box-cP-at02142041 : Ws → St 1164
  lem-box-cP-at02142041 = pickᴰ 160 Sᴰ
  lem-box-cP-at0314203241 : Ws → St 1165
  lem-box-cP-at0314203241 = pickᴰ 161 Sᴰ
  lem-box-cP-at03243042 : Ws → St 1166
  lem-box-cP-at03243042 = pickᴰ 162 Sᴰ
  lem-box-cP-at142142 : Ws → St 1167
  lem-box-cP-at142142 = pickᴰ 163 Sᴰ
  lem-sym-bc-at02102331 : Ws → St 1168
  lem-sym-bc-at02102331 = pickᴰ 164 Sᴰ
  lem-sym-bc-at142142 : Ws → St 1169
  lem-sym-bc-at142142 = pickᴰ 165 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1002 (lem-box-cP-at122441 c4)
  q2 : Ws → Eqn
  q2 c4 = wpE 843 c4
  q3 : Ws → Eqn
  q3 c4 = wpE 845 c4
  q4 : Ws → Eqn
  q4 c4 = wlE 241 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = wpE 89 c4
  q6 : Ws → Eqn
  q6 c4 = wpE 36 c4
  q7 : Ws → Eqn
  q7 c4 = sE 1024 (lem-comm-CCZ024-CX13 c4)
  q8 : Ws → Eqn
  q8 c4 = wpE 35 c4
  q9 : Ws → Eqn
  q9 c4 = wpE 34 c4
  q10 : Ws → Eqn
  q10 c4 = wpE 88 c4
  q11 : Ws → Eqn
  q11 c4 = wpE 97 c4
  q12 : Ws → Eqn
  q12 c4 = wlE 245 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wpE 95 c4
  q14 : Ws → Eqn
  q14 c4 = sE 1059 (lem-comm-TOFF013-CX24 c4)
  q15 : Ws → Eqn
  q15 c4 = wpE 94 c4
  q16 : Ws → Eqn
  q16 c4 = wlE 246 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = wpE 842 c4
  q18 : Ws → Eqn
  q18 c4 = wpE 90 c4
  q19 : Ws → Eqn
  q19 c4 = wlE 247 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = wpE 81 c4
  q21 : Ws → Eqn
  q21 c4 = wlE 244 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = wpE 87 c4
  q23 : Ws → Eqn
  q23 c4 = wlE 1037 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = wlE 305 (lit c4)

-- nf-comm-CS-S0@2: 83 steps
lem-nf-comm-CS-S0at2 : Ws → ⟪ (ℓ "乩侬") ⟫ʷ ≈ ⟪ (ℓ "乩亭乇亭么仞") ⟫ʷ
lem-nf-comm-CS-S0at2 c4 = derive (ℓ "乩侬") (ℓ "乩亭乇亭么仞")
  (re 1 1 (ℓ "仞亭侪亭侫") ∷
   re 3 1 (ℓ "乇") ∷
   re 5 1 (ℓ "么") ∷
   rw 1 (q1 c4) ∷
   rw 4 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q9 c4) ∷
   rw 11 (q10 c4) ∷
   rw 5 (q4 c4) ∷
   rw 2 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw 4 (q14 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 2 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q9 c4) ∷
   rw 8 (q10 c4) ∷
   rw 2 (q4 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw 5 (q20 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 7 (q2 c4) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q6 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q8 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q9 c4) ∷
   rw 14 (q10 c4) ∷
   rw 8 (q4 c4) ∷
   rw 5 (q11 c4) ∷
   rw 7 (q12 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw 7 (q14 c4) ∷
   rw⁻ 8 (q15 c4) ∷
   rw 9 (q14 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q9 c4) ∷
   rw 11 (q10 c4) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw 8 (q22 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   rw 6 (q22 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw 1 (q23 c4) ∷
   rw 3 (q24 c4) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = sE 994 (lem-box-cP-at0210243143 c4)
  q26 : Ws → Eqn
  q26 c4 = wlE 747 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = wpE 654 c4
  q28 : Ws → Eqn
  q28 c4 = wlE 190 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = wpE 37 c4
  q30 : Ws → Eqn
  q30 c4 = wpE 33 c4
  q31 : Ws → Eqn
  q31 c4 = wlE 197 (lit c4)
  q32 : Ws → Eqn
  q32 c4 = wpE 41 c4
  q33 : Ws → Eqn
  q33 c4 = wlE 195 (lit c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1028 (lem-comm-TOFF213-CX04 c4)
  q35 : Ws → Eqn
  q35 c4 = wlE 194 (lit c4)
  q36 : Ws → Eqn
  q36 c4 = wlE 193 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = wpE 44 c4
  q38 : Ws → Eqn
  q38 c4 = wpE 38 c4
  q39 : Ws → Eqn
  q39 c4 = wlE 196 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = wpE 21 c4
  q41 : Ws → Eqn
  q41 c4 = wlE 191 (lit c4)
  q42 : Ws → Eqn
  q42 c4 = wpE 32 c4
  q43 : Ws → Eqn
  q43 c4 = wpE 651 c4
  q44 : Ws → Eqn
  q44 c4 = wpE 161 c4

-- nf-comm-CS-S1@0: 83 steps
lem-nf-comm-CS-S1at0 : Ws → ⟪ (ℓ "乕俄") ⟫ʷ ≈ ⟪ (ℓ "乕亮丶亮丷伱") ⟫ʷ
lem-nf-comm-CS-S1at0 c4 = derive (ℓ "乕俄") (ℓ "乕亮丶亮丷伱")
  (re 1 1 (ℓ "伱亮係亮促") ∷
   re 3 1 (ℓ "丶") ∷
   re 5 1 (ℓ "丷") ∷
   rw 1 (q25 c4) ∷
   rw 4 (q26 c4) ∷
   rw 3 (q27 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw 5 (q29 c4) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q9 c4) ∷
   rw 11 (q30 c4) ∷
   rw 5 (q28 c4) ∷
   rw 2 (q31 c4) ∷
   rw 4 (q32 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   rw 4 (q34 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   rw 6 (q34 c4) ∷
   rw⁻ 7 (q36 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   rw 4 (q26 c4) ∷
   rw⁻ 2 (q37 c4) ∷
   rw⁻ 1 (q38 c4) ∷
   rw⁻ 3 (q28 c4) ∷
   rw 2 (q29 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q9 c4) ∷
   rw 8 (q30 c4) ∷
   rw 2 (q28 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   rw 3 (q25 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw 5 (q40 c4) ∷
   rw⁻ 4 (q39 c4) ∷
   rw 3 (q40 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   rw 4 (q25 c4) ∷
   rw 7 (q26 c4) ∷
   rw 6 (q27 c4) ∷
   rw⁻ 9 (q28 c4) ∷
   rw 8 (q29 c4) ∷
   rw 9 (q6 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q8 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q9 c4) ∷
   rw 14 (q30 c4) ∷
   rw 8 (q28 c4) ∷
   rw 5 (q31 c4) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 6 (q33 c4) ∷
   rw 7 (q34 c4) ∷
   rw⁻ 8 (q35 c4) ∷
   rw 9 (q34 c4) ∷
   rw⁻ 10 (q36 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   rw 7 (q26 c4) ∷
   rw⁻ 5 (q37 c4) ∷
   rw⁻ 4 (q38 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw 5 (q29 c4) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q9 c4) ∷
   rw 11 (q30 c4) ∷
   rw 5 (q28 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw 6 (q25 c4) ∷
   rw⁻ 9 (q41 c4) ∷
   rw 8 (q42 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   rw 6 (q42 c4) ∷
   rw⁻ 7 (q25 c4) ∷
   rw 1 (q43 c4) ∷
   rw 3 (q44 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = sE 1008 (lem-box-cP-at243243 c4)
  q46 : Ws → Eqn
  q46 c4 = wpE 805 c4
  q47 : Ws → Eqn
  q47 c4 = wpE 806 c4
  q48 : Ws → Eqn
  q48 c4 = wlE 217 (lit c4)
  q49 : Ws → Eqn
  q49 c4 = wpE 65 c4
  q50 : Ws → Eqn
  q50 c4 = wpE 64 c4
  q51 : Ws → Eqn
  q51 c4 = sE 893 (lem-comm-CCZ014-CX23 c4)
  q52 : Ws → Eqn
  q52 c4 = wpE 63 c4
  q53 : Ws → Eqn
  q53 c4 = wpE 62 c4
  q54 : Ws → Eqn
  q54 c4 = wpE 61 c4
  q55 : Ws → Eqn
  q55 c4 = wpE 72 c4
  q56 : Ws → Eqn
  q56 c4 = wlE 220 (lit c4)
  q57 : Ws → Eqn
  q57 c4 = wpE 70 c4
  q58 : Ws → Eqn
  q58 c4 = sE 1060 (lem-comm-TOFF023-CX14 c4)
  q59 : Ws → Eqn
  q59 c4 = wpE 69 c4
  q60 : Ws → Eqn
  q60 c4 = wlE 221 (lit c4)
  q61 : Ws → Eqn
  q61 c4 = wpE 74 c4
  q62 : Ws → Eqn
  q62 c4 = wpE 66 c4
  q63 : Ws → Eqn
  q63 c4 = wlE 222 (lit c4)
  q64 : Ws → Eqn
  q64 c4 = wpE 53 c4
  q65 : Ws → Eqn
  q65 c4 = wlE 219 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = wpE 60 c4
  q67 : Ws → Eqn
  q67 c4 = wlE 1000 (lit c4)
  q68 : Ws → Eqn
  q68 c4 = wlE 263 (lit c4)

-- nf-comm-CS-S1@1: 83 steps
lem-nf-comm-CS-S1at1 : Ws → ⟪ (ℓ "乩侧") ⟫ʷ ≈ ⟪ (ℓ "乩亲乎亲乏仄") ⟫ʷ
lem-nf-comm-CS-S1at1 c4 = derive (ℓ "乩侧") (ℓ "乩亲乎亲乏仄")
  (re 1 1 (ℓ "仄亲侥亲侦") ∷
   re 3 1 (ℓ "乎") ∷
   re 5 1 (ℓ "乏") ∷
   rw 1 (q45 c4) ∷
   rw 4 (q46 c4) ∷
   rw 3 (q47 c4) ∷
   rw⁻ 6 (q48 c4) ∷
   rw 5 (q49 c4) ∷
   rw 6 (q50 c4) ∷
   rw 7 (q51 c4) ∷
   rw 8 (q52 c4) ∷
   rw 9 (q51 c4) ∷
   rw 10 (q53 c4) ∷
   rw 11 (q54 c4) ∷
   rw 5 (q48 c4) ∷
   rw 2 (q55 c4) ∷
   rw 4 (q56 c4) ∷
   rw⁻ 3 (q57 c4) ∷
   rw 4 (q58 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw 6 (q58 c4) ∷
   rw⁻ 7 (q60 c4) ∷
   rw⁻ 3 (q56 c4) ∷
   rw 4 (q46 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   rw 2 (q49 c4) ∷
   rw 3 (q50 c4) ∷
   rw 4 (q51 c4) ∷
   rw 5 (q52 c4) ∷
   rw 6 (q51 c4) ∷
   rw 7 (q53 c4) ∷
   rw 8 (q54 c4) ∷
   rw 2 (q48 c4) ∷
   rw⁻ 3 (q45 c4) ∷
   rw 3 (q45 c4) ∷
   rw⁻ 6 (q63 c4) ∷
   rw 5 (q64 c4) ∷
   rw⁻ 4 (q63 c4) ∷
   rw 3 (q64 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   rw 4 (q45 c4) ∷
   rw 7 (q46 c4) ∷
   rw 6 (q47 c4) ∷
   rw⁻ 9 (q48 c4) ∷
   rw 8 (q49 c4) ∷
   rw 9 (q50 c4) ∷
   rw 10 (q51 c4) ∷
   rw 11 (q52 c4) ∷
   rw 12 (q51 c4) ∷
   rw 13 (q53 c4) ∷
   rw 14 (q54 c4) ∷
   rw 8 (q48 c4) ∷
   rw 5 (q55 c4) ∷
   rw 7 (q56 c4) ∷
   rw⁻ 6 (q57 c4) ∷
   rw 7 (q58 c4) ∷
   rw⁻ 8 (q59 c4) ∷
   rw 9 (q58 c4) ∷
   rw⁻ 10 (q60 c4) ∷
   rw⁻ 6 (q56 c4) ∷
   rw 7 (q46 c4) ∷
   rw⁻ 5 (q61 c4) ∷
   rw 4 (q62 c4) ∷
   rw⁻ 6 (q48 c4) ∷
   rw 5 (q49 c4) ∷
   rw 6 (q50 c4) ∷
   rw 7 (q51 c4) ∷
   rw 8 (q52 c4) ∷
   rw 9 (q51 c4) ∷
   rw 10 (q53 c4) ∷
   rw 11 (q54 c4) ∷
   rw 5 (q48 c4) ∷
   rw⁻ 6 (q45 c4) ∷
   rw 6 (q45 c4) ∷
   rw⁻ 9 (q65 c4) ∷
   rw 8 (q66 c4) ∷
   rw⁻ 7 (q65 c4) ∷
   rw 6 (q66 c4) ∷
   rw⁻ 7 (q45 c4) ∷
   rw 1 (q67 c4) ∷
   rw 3 (q68 c4) ∷ []) Eq.refl

-- nf-comm-CS-S1@2: 83 steps
lem-nf-comm-CS-S1at2 : Ws → ⟪ (ℓ "乹侬") ⟫ʷ ≈ ⟪ (ℓ "乹亭乇亭么仞") ⟫ʷ
lem-nf-comm-CS-S1at2 c4 = derive (ℓ "乹侬") (ℓ "乹亭乇亭么仞")
  (re 1 1 (ℓ "仞亭侪亭侫") ∷
   re 3 1 (ℓ "乇") ∷
   re 5 1 (ℓ "么") ∷
   rw 1 (q1 c4) ∷
   rw 4 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q9 c4) ∷
   rw 11 (q10 c4) ∷
   rw 5 (q4 c4) ∷
   rw 2 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw 4 (q14 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 2 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q9 c4) ∷
   rw 8 (q10 c4) ∷
   rw 2 (q4 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw 5 (q20 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 7 (q2 c4) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q6 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q8 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q9 c4) ∷
   rw 14 (q10 c4) ∷
   rw 8 (q4 c4) ∷
   rw 5 (q11 c4) ∷
   rw 7 (q12 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw 7 (q14 c4) ∷
   rw⁻ 8 (q15 c4) ∷
   rw 9 (q14 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q9 c4) ∷
   rw 11 (q10 c4) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw 8 (q22 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   rw 6 (q22 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw 1 (q23 c4) ∷
   rw 3 (q24 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = sE 1082 (lem-P-box-at0214203143 c4)
  q70 : Ws → Eqn
  q70 c4 = sE 1112 (lem-box-cP-at0214203143 c4)
  q71 : Ws → Eqn
  q71 c4 = wlE 180 (lit c4)
  q72 : Ws → Eqn
  q72 c4 = sE 330 (lem-box-tQ-at02233440 c4)

-- pairs @0214203143: 4 steps
lem-pairs-at0214203143 : Ws → ⟪ (ℓ "佔") ⟫ʷ ≈ ⟪ (ℓ "伵") ⟫ʷ
lem-pairs-at0214203143 c4 = derive (ℓ "佔") (ℓ "伵")
  (rw⁻ 0 (q69 c4) ∷
   rw 1 (q70 c4) ∷
   rw 4 (q71 c4) ∷
   rw⁻ 0 (q72 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = sE 1142 (lem-sym-bc-at02233440 c4)

-- box-perm-1324 @02233440: 1 steps
lem-box-perm-1324-at02233440 : Ws → ⟪ (ℓ "伵") ⟫ʷ ≈ ⟪ (ℓ "伶") ⟫ʷ
lem-box-perm-1324-at02233440 c4 = derive (ℓ "伵") (ℓ "伶")
  (rw 0 (q73 c4) ∷ []) Eq.refl

private
  q74 : Ws → Eqn
  q74 c4 = sE 1114 (lem-box-cP-at022440 c4)
  q75 : Ws → Eqn
  q75 c4 = wlE 1127 (lit c4)
  q76 : Ws → Eqn
  q76 c4 = wlE 1128 (lit c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (ℓ "亚並") (ℓ "並亚") (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (X))
  q78 : Ws → Eqn
  q78 c4 = wlE 289 (lit c4)
  q79 : Ws → Eqn
  q79 c4 = wpE 919 c4
  q80 : Ws → Eqn
  q80 c4 = wlE 280 (lit c4)
  q81 : Ws → Eqn
  q81 c4 = sE 959 (lem-comm-CSd03-CCZ124 c4)
  q82 : Ws → Eqn
  q82 c4 = sE 957 (lem-comm-CS03-CCZ124 c4)
  q83 : Ws → Eqn
  q83 c4 = wlE 1129 (lit c4)
  q84 : Ws → Eqn
  q84 c4 = wlE 1130 (lit c4)
  q85 : Ws → Eqn
  q85 c4 = wlE 1131 (lit c4)
  q86 : Ws → Eqn
  q86 c4 = wpE 24 c4

-- Xb-box @022440: 18 steps
lem-Xb-box-at022440 : Ws → ⟪ (ℓ "並伶並") ⟫ʷ ≈ ⟪ (ℓ "伶亐") ⟫ʷ
lem-Xb-box-at022440 c4 = derive (ℓ "並伶並") (ℓ "伶亐")
  (rw 1 (q74 c4) ∷
   rw⁻ 0 (q75 c4) ∷
   rw 2 (q76 c4) ∷
   rw⁻ 1 (q77 c4) ∷
   rw 4 (q78 c4) ∷
   rw⁻ 8 (q79 c4) ∷
   rw⁻ 7 (q80 c4) ∷
   rw 6 (q81 c4) ∷
   rw⁻ 5 (q80 c4) ∷
   rw 4 (q82 c4) ∷
   rw⁻ 5 (q78 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw⁻ 2 (q75 c4) ∷
   rw 3 (q84 c4) ∷
   rw 4 (q85 c4) ∷
   rw⁻ 3 (q77 c4) ∷
   rw⁻ 0 (q74 c4) ∷
   rw⁻ 1 (q86 c4) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = sE 1143 (lem-sym-bc-at022440 c4)

-- box-perm-1324 @022440: 1 steps
lem-box-perm-1324-at022440 : Ws → ⟪ (ℓ "伶") ⟫ʷ ≈ ⟪ (ℓ "伵") ⟫ʷ
lem-box-perm-1324-at022440 c4 = derive (ℓ "伶") (ℓ "伵")
  (rw 0 (q87 c4) ∷ []) Eq.refl

private
  q88 : Ws → Eqn
  q88 c4 = sE 1083 (lem-P-box-at02233440 c4)
  q89 : Ws → Eqn
  q89 c4 = sE 1113 (lem-box-cP-at02233440 c4)
  q90 : Ws → Eqn
  q90 c4 = wpE 19 c4
  q91 : Ws → Eqn
  q91 c4 = sE 249 (lem-box-tQ-at0214203143 c4)

-- pairs @02233440: 4 steps
lem-pairs-at02233440 : Ws → ⟪ (ℓ "伵") ⟫ʷ ≈ ⟪ (ℓ "佔") ⟫ʷ
lem-pairs-at02233440 c4 = derive (ℓ "伵") (ℓ "佔")
  (rw⁻ 0 (q88 c4) ∷
   rw 1 (q89 c4) ∷
   rw 4 (q90 c4) ∷
   rw⁻ 0 (q91 c4) ∷ []) Eq.refl

private
  q92 : Ws → Eqn
  q92 c4 = sE 1157 (lem-sym-bc-at12233441 c4)

-- box-perm-1324 @12233441: 1 steps
lem-box-perm-1324-at12233441 : Ws → ⟪ (ℓ "付") ⟫ʷ ≈ ⟪ (ℓ "仞") ⟫ʷ
lem-box-perm-1324-at12233441 c4 = derive (ℓ "付") (ℓ "仞")
  (rw 0 (q92 c4) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = sE 1092 (lem-P-box-at1441 c4)
  q94 : Ws → Eqn
  q94 c4 = sE 1128 (lem-box-cP-at1441 c4)
  q95 : Ws → Eqn
  q95 c4 = wlE 229 (lit c4)
  q96 : Ws → Eqn
  q96 c4 = sE 259 (lem-box-tQ-at13213442 c4)

-- pairs @1441: 4 steps
lem-pairs-at1441 : Ws → ⟪ (ℓ "伈") ⟫ʷ ≈ ⟪ (ℓ "仩") ⟫ʷ
lem-pairs-at1441 c4 = derive (ℓ "伈") (ℓ "仩")
  (rw⁻ 0 (q93 c4) ∷
   rw 1 (q94 c4) ∷
   rw 4 (q95 c4) ∷
   rw⁻ 0 (q96 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = sE 1019 (lem-sym-bc-at13213442 c4)

-- box-perm-1324 @13213442: 1 steps
lem-box-perm-1324-at13213442 : Ws → ⟪ (ℓ "仩") ⟫ʷ ≈ ⟪ (ℓ "仳") ⟫ʷ
lem-box-perm-1324-at13213442 c4 = derive (ℓ "仩") (ℓ "仳")
  (rw 0 (q97 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = sE 1138 (lem-sym-bc-at0210233441 c4)

-- box-perm-1324 @0210233441: 1 steps
lem-box-perm-1324-at0210233441 : Ws → ⟪ (ℓ "估") ⟫ʷ ≈ ⟪ (ℓ "伲") ⟫ʷ
lem-box-perm-1324-at0210233441 c4 = derive (ℓ "估") (ℓ "伲")
  (rw 0 (q98 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = sE 1110 (lem-box-cP-at02102441 c4)
  q100 : Ws → Eqn
  q100 c4 = wpE 20 c4
  q101 : Ws → Eqn
  q101 c4 = wlE 183 (lit c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (ℓ "亦並") (ℓ "並亦") (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))
  q103 : Ws → Eqn
  q103 c4 = wlE 905 (lit c4)
  q104 : Ws → Eqn
  q104 c4 = wpE 39 c4
  q105 : Ws → Eqn
  q105 c4 = wpE 756 c4
  q106 : Ws → Eqn
  q106 c4 = sE 960 (lem-comm-CSd13-CCZ024 c4)
  q107 : Ws → Eqn
  q107 c4 = sE 958 (lem-comm-CS13-CCZ024 c4)
  q108 : Ws → Eqn
  q108 c4 = wpE 23 c4
  q109 : Ws → Eqn
  q109 c4 = wlE 185 (lit c4)
  q110 : Ws → Eqn
  q110 c4 = wlE 186 (lit c4)

-- Xb-box @02102441: 18 steps
lem-Xb-box-at02102441 : Ws → ⟪ (ℓ "並伲並") ⟫ʷ ≈ ⟪ (ℓ "伲亐") ⟫ʷ
lem-Xb-box-at02102441 c4 = derive (ℓ "並伲並") (ℓ "伲亐")
  (rw 1 (q99 c4) ∷
   rw⁻ 0 (q100 c4) ∷
   rw 2 (q101 c4) ∷
   rw⁻ 1 (q102 c4) ∷
   rw 4 (q103 c4) ∷
   rw⁻ 8 (q104 c4) ∷
   rw⁻ 7 (q105 c4) ∷
   rw 6 (q106 c4) ∷
   rw⁻ 5 (q105 c4) ∷
   rw 4 (q107 c4) ∷
   rw⁻ 5 (q103 c4) ∷
   rw⁻ 3 (q108 c4) ∷
   rw⁻ 2 (q100 c4) ∷
   rw 3 (q109 c4) ∷
   rw 4 (q110 c4) ∷
   rw⁻ 3 (q102 c4) ∷
   rw⁻ 0 (q99 c4) ∷
   rw⁻ 1 (q86 c4) ∷ []) Eq.refl

private
  q111 : Ws → Eqn
  q111 c4 = sE 1139 (lem-sym-bc-at02102441 c4)

-- box-perm-1324 @02102441: 1 steps
lem-box-perm-1324-at02102441 : Ws → ⟪ (ℓ "伲") ⟫ʷ ≈ ⟪ (ℓ "估") ⟫ʷ
lem-box-perm-1324-at02102441 c4 = derive (ℓ "伲") (ℓ "估")
  (rw 0 (q111 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = sE 1161 (lem-sym-bc-at233442 c4)

-- box-perm-1324 @233442: 1 steps
lem-box-perm-1324-at233442 : Ws → ⟪ (ℓ "仂") ⟫ʷ ≈ ⟪ (ℓ "仆") ⟫ʷ
lem-box-perm-1324-at233442 c4 = derive (ℓ "仂") (ℓ "仆")
  (rw 0 (q112 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = sE 1130 (lem-box-cP-at2442 c4)
  q114 : Ws → Eqn
  q114 c4 = wpE 52 c4
  q115 : Ws → Eqn
  q115 c4 = wlE 206 (lit c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (ℓ "亙並") (ℓ "並亙") (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))
  q117 : Ws → Eqn
  q117 c4 = wlE 242 (lit c4)
  q118 : Ws → Eqn
  q118 c4 = wpE 67 c4
  q119 : Ws → Eqn
  q119 c4 = wpE 795 c4
  q120 : Ws → Eqn
  q120 c4 = sE 704 (lem-comm-CSd23-CCZ014 c4)
  q121 : Ws → Eqn
  q121 c4 = sE 703 (lem-comm-CS23-CCZ014 c4)
  q122 : Ws → Eqn
  q122 c4 = wpE 55 c4
  q123 : Ws → Eqn
  q123 c4 = wlE 208 (lit c4)
  q124 : Ws → Eqn
  q124 c4 = wlE 209 (lit c4)
  q125 : Ws → Eqn
  q125 c4 = wlE 210 (lit c4)

-- Xb-box @2442: 18 steps
lem-Xb-box-at2442 : Ws → ⟪ (ℓ "並仆並") ⟫ʷ ≈ ⟪ (ℓ "仆交") ⟫ʷ
lem-Xb-box-at2442 c4 = derive (ℓ "並仆並") (ℓ "仆交")
  (rw 1 (q113 c4) ∷
   rw⁻ 0 (q114 c4) ∷
   rw 2 (q115 c4) ∷
   rw⁻ 1 (q116 c4) ∷
   rw 4 (q117 c4) ∷
   rw⁻ 8 (q118 c4) ∷
   rw⁻ 7 (q119 c4) ∷
   rw 6 (q120 c4) ∷
   rw⁻ 5 (q119 c4) ∷
   rw 4 (q121 c4) ∷
   rw⁻ 5 (q117 c4) ∷
   rw⁻ 3 (q122 c4) ∷
   rw⁻ 2 (q114 c4) ∷
   rw 3 (q123 c4) ∷
   rw 4 (q124 c4) ∷
   rw⁻ 3 (q116 c4) ∷
   rw⁻ 0 (q113 c4) ∷
   rw⁻ 1 (q125 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = sE 1162 (lem-sym-bc-at2442 c4)

-- box-perm-1324 @2442: 1 steps
lem-box-perm-1324-at2442 : Ws → ⟪ (ℓ "仆") ⟫ʷ ≈ ⟪ (ℓ "仂") ⟫ʷ
lem-box-perm-1324-at2442 c4 = derive (ℓ "仆") (ℓ "仂")
  (rw 0 (q126 c4) ∷ []) Eq.refl

private
  q127 : Ws → Eqn
  q127 c4 = sE 1093 (lem-P-box-at233442 c4)
  q128 : Ws → Eqn
  q128 c4 = sE 1129 (lem-box-cP-at233442 c4)
  q129 : Ws → Eqn
  q129 c4 = wpE 80 c4
  q130 : Ws → Eqn
  q130 c4 = sE 314 (lem-box-tQ-at143143 c4)

-- pairs @233442: 4 steps
lem-pairs-at233442 : Ws → ⟪ (ℓ "仂") ⟫ʷ ≈ ⟪ (ℓ "伅") ⟫ʷ
lem-pairs-at233442 c4 = derive (ℓ "仂") (ℓ "伅")
  (rw⁻ 0 (q127 c4) ∷
   rw 1 (q128 c4) ∷
   rw 4 (q129 c4) ∷
   rw⁻ 0 (q130 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = sE 1156 (lem-sym-bc-at12213443 c4)

-- box-perm-1324 @12213443: 1 steps
lem-box-perm-1324-at12213443 : Ws → ⟪ (ℓ "仑") ⟫ʷ ≈ ⟪ (ℓ "仛") ⟫ʷ
lem-box-perm-1324-at12213443 c4 = derive (ℓ "仑") (ℓ "仛")
  (rw 0 (q131 c4) ∷ []) Eq.refl

private
  q132 : Ws → Eqn
  q132 c4 = sE 1127 (lem-box-cP-at12243143 c4)
  q133 : Ws → Eqn
  q133 c4 = wlE 232 (lit c4)
  q134 : Ws → Eqn
  q134 c4 = eqn (ℓ "云並") (ℓ "並云") (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))
  q135 : Ws → Eqn
  q135 c4 = wlE 326 (lit c4)
  q136 : Ws → Eqn
  q136 c4 = wpE 92 c4
  q137 : Ws → Eqn
  q137 c4 = wpE 749 c4
  q138 : Ws → Eqn
  q138 c4 = wlE 234 (lit c4)

-- Xb-box @12243143: 18 steps
lem-Xb-box-at12243143 : Ws → ⟪ (ℓ "並仛並") ⟫ʷ ≈ ⟪ (ℓ "仛交") ⟫ʷ
lem-Xb-box-at12243143 c4 = derive (ℓ "並仛並") (ℓ "仛交")
  (rw 1 (q132 c4) ∷
   rw⁻ 0 (q100 c4) ∷
   rw 2 (q133 c4) ∷
   rw⁻ 1 (q134 c4) ∷
   rw 4 (q135 c4) ∷
   rw⁻ 8 (q136 c4) ∷
   rw⁻ 7 (q137 c4) ∷
   rw 6 (q106 c4) ∷
   rw⁻ 5 (q137 c4) ∷
   rw 4 (q107 c4) ∷
   rw⁻ 5 (q135 c4) ∷
   rw⁻ 3 (q108 c4) ∷
   rw⁻ 2 (q100 c4) ∷
   rw 3 (q109 c4) ∷
   rw 4 (q138 c4) ∷
   rw⁻ 3 (q134 c4) ∷
   rw⁻ 0 (q132 c4) ∷
   rw⁻ 1 (q125 c4) ∷ []) Eq.refl

private
  q139 : Ws → Eqn
  q139 c4 = sE 1158 (lem-sym-bc-at12243143 c4)

-- box-perm-1324 @12243143: 1 steps
lem-box-perm-1324-at12243143 : Ws → ⟪ (ℓ "仛") ⟫ʷ ≈ ⟪ (ℓ "仑") ⟫ʷ
lem-box-perm-1324-at12243143 c4 = derive (ℓ "仛") (ℓ "仑")
  (rw 0 (q139 c4) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = sE 1091 (lem-P-box-at12213443 c4)
  q141 : Ws → Eqn
  q141 c4 = sE 1126 (lem-box-cP-at12213443 c4)
  q142 : Ws → Eqn
  q142 c4 = wpE 6 c4
  q143 : Ws → Eqn
  q143 c4 = sE 88 (lem-box-tQ-at14233241 c4)

-- pairs @12213443: 4 steps
lem-pairs-at12213443 : Ws → ⟪ (ℓ "仑") ⟫ʷ ≈ ⟪ (ℓ "伍") ⟫ʷ
lem-pairs-at12213443 c4 = derive (ℓ "仑") (ℓ "伍")
  (rw⁻ 0 (q140 c4) ∷
   rw 1 (q141 c4) ∷
   rw 4 (q142 c4) ∷
   rw⁻ 0 (q143 c4) ∷ []) Eq.refl

private
  q144 : Ws → Eqn
  q144 c4 = sE 1071 (lem-sym-ab-at243243 c4)
  q145 : Ws → Eqn
  q145 c4 = sE 1159 (lem-sym-bc-at14213243 c4)

-- box-perm-2314 @243243: 2 steps
lem-box-perm-2314-at243243 : Ws → ⟪ (ℓ "仄") ⟫ʷ ≈ ⟪ (ℓ "伅") ⟫ʷ
lem-box-perm-2314-at243243 c4 = derive (ℓ "仄") (ℓ "伅")
  (rw 0 (q144 c4) ∷
   rw 0 (q145 c4) ∷ []) Eq.refl

private
  q146 : Ws → Eqn
  q146 c4 = sE 1153 (lem-sym-bc-at03143140 c4)

-- box-perm-1324 @03143140: 1 steps
lem-box-perm-1324-at03143140 : Ws → ⟪ (ℓ "侌") ⟫ʷ ≈ ⟪ (ℓ "侅") ⟫ʷ
lem-box-perm-1324-at03143140 c4 = derive (ℓ "侌") (ℓ "侅")
  (rw 0 (q146 c4) ∷ []) Eq.refl

private
  q147 : Ws → Eqn
  q147 c4 = sE 1076 (lem-sym-ab-at0314213240 c4)

-- box-perm-3124 @03143140: 2 steps
lem-box-perm-3124-at03143140 : Ws → ⟪ (ℓ "侌") ⟫ʷ ≈ ⟪ (ℓ "佯") ⟫ʷ
lem-box-perm-3124-at03143140 c4 = derive (ℓ "侌") (ℓ "佯")
  (rw 0 (q146 c4) ∷
   rw 0 (q147 c4) ∷ []) Eq.refl

private
  q148 : Ws → Eqn
  q148 c4 = sE 358 (lem-box-tQ-at03243240 c4)
  q149 : Ws → Eqn
  q149 c4 = sE 1004 (lem-box-cP-at13213442 c4)
  q150 : Ws → Eqn
  q150 c4 = wlE 671 (lit c4)
  q151 : Ws → Eqn
  q151 c4 = wpE 993 c4
  q152 : Ws → Eqn
  q152 c4 = wlE 293 (lit c4)
  q153 : Ws → Eqn
  q153 c4 = wlE 324 (lit c4)
  q154 : Ws → Eqn
  q154 c4 = wpE 523 c4
  q155 : Ws → Eqn
  q155 c4 = sE 204 (lem-comm-CSd24-CCZ013 c4)
  q156 : Ws → Eqn
  q156 c4 = sE 194 (lem-comm-CS24-CCZ013 c4)
  q157 : Ws → Eqn
  q157 c4 = wpE 994 c4
  q158 : Ws → Eqn
  q158 c4 = wpE 990 c4
  q159 : Ws → Eqn
  q159 c4 = wlE 1182 (lit c4)
  q160 : Ws → Eqn
  q160 c4 = wpE 740 c4
  q161 : Ws → Eqn
  q161 c4 = wpE 970 c4
  q162 : Ws → Eqn
  q162 c4 = sE 1069 (lem-comm-CX31-TOFF024 c4)
  q163 : Ws → Eqn
  q163 c4 = wpE 995 c4
  q164 : Ws → Eqn
  q164 c4 = wpE 590 c4
  q165 : Ws → Eqn
  q165 c4 = wpE 742 c4
  q166 : Ws → Eqn
  q166 c4 = wpE 394 c4
  q167 : Ws → Eqn
  q167 c4 = wlE 645 (lit c4)
  q168 : Ws → Eqn
  q168 c4 = wpE 189 c4
  q169 : Ws → Eqn
  q169 c4 = wpE 996 c4
  q170 : Ws → Eqn
  q170 c4 = wpE 743 c4
  q171 : Ws → Eqn
  q171 c4 = wlE 621 (lit c4)
  q172 : Ws → Eqn
  q172 c4 = sE 4 (lem-comm-CX14-CCZ023 c4)
  q173 : Ws → Eqn
  q173 c4 = wpE 820 c4
  q174 : Ws → Eqn
  q174 c4 = wpE 513 c4
  q175 : Ws → Eqn
  q175 c4 = wlE 974 (lit c4)

-- box-box-4 @03243240: 103 steps
lem-box-box-4-at03243240 : Ws → ⟪ (ℓ "佯仩") ⟫ʷ ≈ ⟪ (ℓ "仩佯") ⟫ʷ
lem-box-box-4-at03243240 c4 = derive (ℓ "佯仩") (ℓ "仩佯")
  (rw 0 (q148 c4) ∷
   rw 4 (q149 c4) ∷
   rw⁻ 3 (q150 c4) ∷
   rw 4 (q151 c4) ∷
   rw⁻ 6 (q150 c4) ∷
   rw 5 (q152 c4) ∷
   rw⁻ 9 (q153 c4) ∷
   rw⁻ 8 (q154 c4) ∷
   rw 7 (q155 c4) ∷
   rw⁻ 6 (q154 c4) ∷
   rw 5 (q156 c4) ∷
   rw⁻ 6 (q152 c4) ∷
   rw 6 (q157 c4) ∷
   rw⁻ 3 (q149 c4) ∷
   rw 3 (q149 c4) ∷
   rw⁻ 2 (q158 c4) ∷
   rw 4 (q47 c4) ∷
   rw⁻ 3 (q159 c4) ∷
   rw 9 (q160 c4) ∷
   rw 8 (q161 c4) ∷
   rw 7 (q162 c4) ∷
   rw 6 (q163 c4) ∷
   rw 5 (q162 c4) ∷
   rw 4 (q164 c4) ∷
   rw 3 (q165 c4) ∷
   rw 4 (q159 c4) ∷
   rw⁻ 6 (q166 c4) ∷
   rw 5 (q56 c4) ∷
   rw⁻ 9 (q167 c4) ∷
   rw⁻ 8 (q168 c4) ∷
   rw 7 (q155 c4) ∷
   rw⁻ 6 (q168 c4) ∷
   rw 5 (q156 c4) ∷
   rw⁻ 6 (q56 c4) ∷
   rw⁻ 4 (q158 c4) ∷
   rw 6 (q169 c4) ∷
   rw 6 (q170 c4) ∷
   rw⁻ 5 (q159 c4) ∷
   rw 11 (q160 c4) ∷
   rw 10 (q161 c4) ∷
   rw 9 (q162 c4) ∷
   rw 8 (q163 c4) ∷
   rw 7 (q162 c4) ∷
   rw 6 (q164 c4) ∷
   rw 5 (q165 c4) ∷
   rw 6 (q159 c4) ∷
   rw⁻ 2 (q149 c4) ∷
   rw 2 (q149 c4) ∷
   rw⁻ 1 (q150 c4) ∷
   rw 2 (q151 c4) ∷
   rw⁻ 4 (q150 c4) ∷
   rw 3 (q152 c4) ∷
   rw⁻ 7 (q153 c4) ∷
   rw⁻ 6 (q154 c4) ∷
   rw 5 (q155 c4) ∷
   rw⁻ 4 (q154 c4) ∷
   rw 3 (q156 c4) ∷
   rw⁻ 4 (q152 c4) ∷
   rw 4 (q157 c4) ∷
   rw⁻ 1 (q149 c4) ∷
   rw 1 (q149 c4) ∷
   rw⁻ 0 (q158 c4) ∷
   rw 2 (q47 c4) ∷
   rw⁻ 1 (q159 c4) ∷
   rw 7 (q160 c4) ∷
   rw 6 (q161 c4) ∷
   rw 5 (q162 c4) ∷
   rw 4 (q163 c4) ∷
   rw 3 (q162 c4) ∷
   rw 2 (q164 c4) ∷
   rw 1 (q165 c4) ∷
   rw 2 (q159 c4) ∷
   rw⁻ 4 (q166 c4) ∷
   rw 3 (q56 c4) ∷
   rw⁻ 7 (q167 c4) ∷
   rw⁻ 6 (q168 c4) ∷
   rw 5 (q155 c4) ∷
   rw⁻ 4 (q168 c4) ∷
   rw 3 (q156 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw⁻ 2 (q158 c4) ∷
   rw 4 (q169 c4) ∷
   rw 4 (q170 c4) ∷
   rw⁻ 3 (q159 c4) ∷
   rw 9 (q160 c4) ∷
   rw 8 (q161 c4) ∷
   rw 7 (q162 c4) ∷
   rw 6 (q163 c4) ∷
   rw 5 (q162 c4) ∷
   rw 4 (q164 c4) ∷
   rw 3 (q165 c4) ∷
   rw 4 (q159 c4) ∷
   rw⁻ 0 (q149 c4) ∷
   rw 2 (q56 c4) ∷
   rw⁻ 6 (q171 c4) ∷
   rw 5 (q172 c4) ∷
   rw⁻ 4 (q173 c4) ∷
   rw 3 (q172 c4) ∷
   rw⁻ 2 (q174 c4) ∷
   rw⁻ 3 (q56 c4) ∷
   rw 3 (q175 c4) ∷
   rw 4 (q68 c4) ∷
   rw⁻ 1 (q148 c4) ∷ []) Eq.refl

private
  q176 : Ws → Eqn
  q176 c4 = sE 1078 (lem-sym-ab-at03243240 c4)
  q177 : Ws → Eqn
  q177 c4 = sE 1151 (lem-sym-bc-at0314213240 c4)

-- box-perm-2314 @03243240: 2 steps
lem-box-perm-2314-at03243240 : Ws → ⟪ (ℓ "佯") ⟫ʷ ≈ ⟪ (ℓ "侌") ⟫ʷ
lem-box-perm-2314-at03243240 c4 = derive (ℓ "佯") (ℓ "侌")
  (rw 0 (q176 c4) ∷
   rw 0 (q177 c4) ∷ []) Eq.refl

private
  q178 : Ws → Eqn
  q178 c4 = sE 1123 (lem-box-cP-at03143140 c4)
  q179 : Ws → Eqn
  q179 c4 = wlE 432 (lit c4)
  q180 : Ws → Eqn
  q180 c4 = wlE 1191 (lit c4)
  q181 : Ws → Eqn
  q181 c4 = wlE 323 (lit c4)
  q182 : Ws → Eqn
  q182 c4 = wpE 294 c4
  q183 : Ws → Eqn
  q183 c4 = wlE 336 (lit c4)
  q184 : Ws → Eqn
  q184 c4 = eqn (ℓ "丩亰") (ℓ "亰丩") (c₂ (CS • CS • CS) (CCZ))
  q185 : Ws → Eqn
  q185 c4 = eqn (ℓ "丨亰") (ℓ "亰丨") (c₂ (CS) (CCZ))
  q186 : Ws → Eqn
  q186 c4 = wlE 1192 (lit c4)
  q187 : Ws → Eqn
  q187 c4 = wlE 1193 (lit c4)
  q188 : Ws → Eqn
  q188 c4 = wlE 1194 (lit c4)

-- CSdu-box-3 @03143140: 17 steps
lem-CSdu-box-3-at03143140 : Ws → ⟪ (ℓ "乏侌") ⟫ʷ ≈ ⟪ (ℓ "侌乏") ⟫ʷ
lem-CSdu-box-3-at03143140 c4 = derive (ℓ "乏侌") (ℓ "侌乏")
  (rw 1 (q178 c4) ∷
   rw⁻ 0 (q179 c4) ∷
   rw 1 (q180 c4) ∷
   rw 4 (q181 c4) ∷
   rw⁻ 8 (q182 c4) ∷
   rw⁻ 7 (q183 c4) ∷
   rw 6 (q184 c4) ∷
   rw⁻ 5 (q183 c4) ∷
   rw 4 (q185 c4) ∷
   rw⁻ 5 (q181 c4) ∷
   rw 3 (q184 c4) ∷
   rw⁻ 2 (q179 c4) ∷
   rw 5 (q186 c4) ∷
   rw 4 (q187 c4) ∷
   rw 3 (q180 c4) ∷
   rw 4 (q188 c4) ∷
   rw⁻ 0 (q178 c4) ∷ []) Eq.refl

private
  q189 : Ws → Eqn
  q189 c4 = wlE 433 (lit c4)
  q190 : Ws → Eqn
  q190 c4 = wlE 1200 (lit c4)
  q191 : Ws → Eqn
  q191 c4 = wlE 1201 (lit c4)
  q192 : Ws → Eqn
  q192 c4 = wlE 1202 (lit c4)

-- CSu-box-3 @03143140: 17 steps
lem-CSu-box-3-at03143140 : Ws → ⟪ (ℓ "乎侌") ⟫ʷ ≈ ⟪ (ℓ "侌乎") ⟫ʷ
lem-CSu-box-3-at03143140 c4 = derive (ℓ "乎侌") (ℓ "侌乎")
  (rw 1 (q178 c4) ∷
   rw⁻ 0 (q189 c4) ∷
   rw 1 (q190 c4) ∷
   rw 4 (q181 c4) ∷
   rw⁻ 8 (q182 c4) ∷
   rw⁻ 7 (q183 c4) ∷
   rw 6 (q184 c4) ∷
   rw⁻ 5 (q183 c4) ∷
   rw 4 (q185 c4) ∷
   rw⁻ 5 (q181 c4) ∷
   rw 3 (q185 c4) ∷
   rw⁻ 2 (q189 c4) ∷
   rw 5 (q186 c4) ∷
   rw 4 (q191 c4) ∷
   rw 3 (q190 c4) ∷
   rw 4 (q192 c4) ∷
   rw⁻ 0 (q178 c4) ∷ []) Eq.refl

private
  q193 : Ws → Eqn
  q193 c4 = sE 357 (lem-box-tQ-at03143140 c4)
  q194 : Ws → Eqn
  q194 c4 = wlE 442 (lit c4)
  q195 : Ws → Eqn
  q195 c4 = sE 1095 (lem-t-cP-at03143140 c4)
  q196 : Ws → Eqn
  q196 c4 = wlE 230 (lit c4)

-- box2 @03143140: 11 steps
lem-box2-at03143140 : Ws → ⟪ (ℓ "侌侌") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at03143140 c4 = derive (ℓ "侌侌") []
  (rw 0 (q193 c4) ∷
   rw 4 (q178 c4) ∷
   rw⁻ 4 (q194 c4) ∷
   rw 5 (q195 c4) ∷
   rw⁻ 5 (q178 c4) ∷
   rw 5 (q193 c4) ∷
   rw 4 (q194 c4) ∷
   rw 3 (q196 c4) ∷
   rw 2 (q194 c4) ∷
   rw 1 (q196 c4) ∷
   rw 0 (q194 c4) ∷ []) Eq.refl

private
  q197 : Ws → Eqn
  q197 c4 = sE 1160 (lem-sym-bc-at143143 c4)
  q198 : Ws → Eqn
  q198 c4 = sE 1079 (lem-sym-ab-at14213243 c4)

-- box-perm-3124 @143143: 2 steps
lem-box-perm-3124-at143143 : Ws → ⟪ (ℓ "伅") ⟫ʷ ≈ ⟪ (ℓ "仄") ⟫ʷ
lem-box-perm-3124-at143143 c4 = derive (ℓ "伅") (ℓ "仄")
  (rw 0 (q197 c4) ∷
   rw 0 (q198 c4) ∷ []) Eq.refl

private
  q199 : Ws → Eqn
  q199 c4 = wpE 1010 c4
  q200 : Ws → Eqn
  q200 c4 = wlE 698 (lit c4)
  q201 : Ws → Eqn
  q201 c4 = sE 1056 (lem-comm-CX14-TOFF023 c4)
  q202 : Ws → Eqn
  q202 c4 = wpE 823 c4
  q203 : Ws → Eqn
  q203 c4 = wpE 725 c4
  q204 : Ws → Eqn
  q204 c4 = wlE 1207 (lit c4)
  q205 : Ws → Eqn
  q205 c4 = wpE 272 c4
  q206 : Ws → Eqn
  q206 c4 = wpE 1011 c4

-- CXu-box-4 @243243: 15 steps
lem-CXu-box-4-at243243 : Ws → ⟪ (ℓ "买仄") ⟫ʷ ≈ ⟪ (ℓ "仄买") ⟫ʷ
lem-CXu-box-4-at243243 c4 = derive (ℓ "买仄") (ℓ "仄买")
  (rw 1 (q45 c4) ∷
   rw⁻ 0 (q199 c4) ∷
   rw 2 (q200 c4) ∷
   rw 6 (q63 c4) ∷
   rw 5 (q201 c4) ∷
   rw 4 (q202 c4) ∷
   rw 3 (q201 c4) ∷
   rw 2 (q203 c4) ∷
   rw⁻ 3 (q200 c4) ∷
   rw 1 (q204 c4) ∷
   rw⁻ 3 (q205 c4) ∷
   rw⁻ 2 (q199 c4) ∷
   rw 3 (q206 c4) ∷
   rw 3 (q204 c4) ∷
   rw⁻ 0 (q45 c4) ∷ []) Eq.refl

private
  q207 : Ws → Eqn
  q207 c4 = sE 1086 (lem-P-box-at0314203142 c4)
  q208 : Ws → Eqn
  q208 c4 = sE 997 (lem-box-cP-at0314203142 c4)
  q209 : Ws → Eqn
  q209 c4 = wlE 489 (lit c4)
  q210 : Ws → Eqn
  q210 c4 = sE 340 (lem-box-tQ-at033440 c4)

-- pairs @0314203142: 4 steps
lem-pairs-at0314203142 : Ws → ⟪ (ℓ "佹") ⟫ʷ ≈ ⟪ (ℓ "佭") ⟫ʷ
lem-pairs-at0314203142 c4 = derive (ℓ "佹") (ℓ "佭")
  (rw⁻ 0 (q207 c4) ∷
   rw 1 (q208 c4) ∷
   rw 4 (q209 c4) ∷
   rw⁻ 0 (q210 c4) ∷ []) Eq.refl

private
  q211 : Ws → Eqn
  q211 c4 = sE 1124 (lem-box-cP-at03243240 c4)
  q212 : Ws → Eqn
  q212 c4 = wlE 788 (lit c4)
  q213 : Ws → Eqn
  q213 c4 = sE 1096 (lem-t-cP-at03243240 c4)
  q214 : Ws → Eqn
  q214 c4 = wlE 204 (lit c4)

-- box2 @03243240: 11 steps
lem-box2-at03243240 : Ws → ⟪ (ℓ "佯佯") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at03243240 c4 = derive (ℓ "佯佯") []
  (rw 0 (q148 c4) ∷
   rw 4 (q211 c4) ∷
   rw⁻ 4 (q212 c4) ∷
   rw 5 (q213 c4) ∷
   rw⁻ 5 (q211 c4) ∷
   rw 5 (q148 c4) ∷
   rw 4 (q212 c4) ∷
   rw 3 (q214 c4) ∷
   rw 2 (q212 c4) ∷
   rw 1 (q214 c4) ∷
   rw 0 (q212 c4) ∷ []) Eq.refl

private
  q215 : Ws → Eqn
  q215 c4 = sE 1154 (lem-sym-bc-at03243240 c4)

-- box-perm-1324 @03243240: 1 steps
lem-box-perm-1324-at03243240 : Ws → ⟪ (ℓ "佯") ⟫ʷ ≈ ⟪ (ℓ "佭") ⟫ʷ
lem-box-perm-1324-at03243240 c4 = derive (ℓ "佯") (ℓ "佭")
  (rw 0 (q215 c4) ∷ []) Eq.refl

private
  q216 : Ws → Eqn
  q216 c4 = sE 1090 (lem-P-box-at033440 c4)
  q217 : Ws → Eqn
  q217 c4 = sE 1125 (lem-box-cP-at033440 c4)
  q218 : Ws → Eqn
  q218 c4 = wpE 351 c4
  q219 : Ws → Eqn
  q219 c4 = sE 310 (lem-box-tQ-at0314203142 c4)

-- pairs @033440: 4 steps
lem-pairs-at033440 : Ws → ⟪ (ℓ "佭") ⟫ʷ ≈ ⟪ (ℓ "佹") ⟫ʷ
lem-pairs-at033440 c4 = derive (ℓ "佭") (ℓ "佹")
  (rw⁻ 0 (q216 c4) ∷
   rw 1 (q217 c4) ∷
   rw 4 (q218 c4) ∷
   rw⁻ 0 (q219 c4) ∷ []) Eq.refl

private
  q220 : Ws → Eqn
  q220 c4 = sE 251 (lem-box-tQ-at0310243142 c4)
  q221 : Ws → Eqn
  q221 c4 = sE 996 (lem-box-cP-at0310243142 c4)
  q222 : Ws → Eqn
  q222 c4 = sE 1094 (lem-t-cP-at0310243142 c4)
  q223 : Ws → Eqn
  q223 c4 = wlE 181 (lit c4)

-- box2 @0310243142: 11 steps
lem-box2-at0310243142 : Ws → ⟪ (ℓ "佨佨") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0310243142 c4 = derive (ℓ "佨佨") []
  (rw 0 (q220 c4) ∷
   rw 4 (q221 c4) ∷
   rw⁻ 4 (q218 c4) ∷
   rw 5 (q222 c4) ∷
   rw⁻ 5 (q221 c4) ∷
   rw 5 (q220 c4) ∷
   rw 4 (q218 c4) ∷
   rw 3 (q223 c4) ∷
   rw 2 (q218 c4) ∷
   rw 1 (q223 c4) ∷
   rw 0 (q218 c4) ∷ []) Eq.refl

private
  q224 : Ws → Eqn
  q224 c4 = sE 1087 (lem-P-box-at0314213042 c4)
  q225 : Ws → Eqn
  q225 c4 = sE 1046 (lem-box-cP-at0314213042 c4)
  q226 : Ws → Eqn
  q226 c4 = wlE 787 (lit c4)
  q227 : Ws → Eqn
  q227 c4 = sE 352 (lem-box-tQ-at03103441 c4)

-- pairs @0314213042: 4 steps
lem-pairs-at0314213042 : Ws → ⟪ (ℓ "侂") ⟫ʷ ≈ ⟪ (ℓ "佧") ⟫ʷ
lem-pairs-at0314213042 c4 = derive (ℓ "侂") (ℓ "佧")
  (rw⁻ 0 (q224 c4) ∷
   rw 1 (q225 c4) ∷
   rw 4 (q226 c4) ∷
   rw⁻ 0 (q227 c4) ∷ []) Eq.refl

private
  q228 : Ws → Eqn
  q228 c4 = sE 1147 (lem-sym-bc-at03103441 c4)

-- box-perm-1324 @03103441: 1 steps
lem-box-perm-1324-at03103441 : Ws → ⟪ (ℓ "佧") ⟫ʷ ≈ ⟪ (ℓ "佩") ⟫ʷ
lem-box-perm-1324-at03103441 c4 = derive (ℓ "佧") (ℓ "佩")
  (rw 0 (q228 c4) ∷ []) Eq.refl

private
  q229 : Ws → Eqn
  q229 c4 = sE 1115 (lem-box-cP-at0310243241 c4)
  q230 : Ws → Eqn
  q230 c4 = wpE 796 c4
  q231 : Ws → Eqn
  q231 c4 = wlE 512 (lit c4)
  q232 : Ws → Eqn
  q232 c4 = eqn (ℓ "产並") (ℓ "並产") (c₄ (Toffᵗ ↑) (X))
  q233 : Ws → Eqn
  q233 c4 = wlE 391 (lit c4)
  q234 : Ws → Eqn
  q234 c4 = wpE 1 c4
  q235 : Ws → Eqn
  q235 c4 = wpE 333 c4
  q236 : Ws → Eqn
  q236 c4 = sE 199 (lem-comm-CSd12-CCZ034 c4)
  q237 : Ws → Eqn
  q237 c4 = sE 191 (lem-comm-CS12-CCZ034 c4)
  q238 : Ws → Eqn
  q238 c4 = wpE 797 c4
  q239 : Ws → Eqn
  q239 c4 = wpE 798 c4
  q240 : Ws → Eqn
  q240 c4 = wlE 503 (lit c4)
  q241 : Ws → Eqn
  q241 c4 = wlE 1243 (lit c4)

-- Xb-box @0310243241: 18 steps
lem-Xb-box-at0310243241 : Ws → ⟪ (ℓ "並佩並") ⟫ʷ ≈ ⟪ (ℓ "佩二") ⟫ʷ
lem-Xb-box-at0310243241 c4 = derive (ℓ "並佩並") (ℓ "佩二")
  (rw 1 (q229 c4) ∷
   rw⁻ 0 (q230 c4) ∷
   rw 2 (q231 c4) ∷
   rw⁻ 1 (q232 c4) ∷
   rw 4 (q233 c4) ∷
   rw⁻ 8 (q234 c4) ∷
   rw⁻ 7 (q235 c4) ∷
   rw 6 (q236 c4) ∷
   rw⁻ 5 (q235 c4) ∷
   rw 4 (q237 c4) ∷
   rw⁻ 5 (q233 c4) ∷
   rw⁻ 3 (q238 c4) ∷
   rw⁻ 2 (q230 c4) ∷
   rw 3 (q239 c4) ∷
   rw 4 (q240 c4) ∷
   rw⁻ 3 (q232 c4) ∷
   rw⁻ 0 (q229 c4) ∷
   rw⁻ 1 (q241 c4) ∷ []) Eq.refl

private
  q242 : Ws → Eqn
  q242 c4 = sE 1145 (lem-sym-bc-at0310243241 c4)

-- box-perm-1324 @0310243241: 1 steps
lem-box-perm-1324-at0310243241 : Ws → ⟪ (ℓ "佩") ⟫ʷ ≈ ⟪ (ℓ "佧") ⟫ʷ
lem-box-perm-1324-at0310243241 c4 = derive (ℓ "佩") (ℓ "佧")
  (rw 0 (q242 c4) ∷ []) Eq.refl

private
  q243 : Ws → Eqn
  q243 c4 = sE 1084 (lem-P-box-at03103441 c4)
  q244 : Ws → Eqn
  q244 c4 = sE 1117 (lem-box-cP-at03103441 c4)
  q245 : Ws → Eqn
  q245 c4 = sE 311 (lem-box-tQ-at0314213042 c4)

-- pairs @03103441: 4 steps
lem-pairs-at03103441 : Ws → ⟪ (ℓ "佧") ⟫ʷ ≈ ⟪ (ℓ "侂") ⟫ʷ
lem-pairs-at03103441 c4 = derive (ℓ "佧") (ℓ "侂")
  (rw⁻ 0 (q243 c4) ∷
   rw 1 (q244 c4) ∷
   rw 4 (q212 c4) ∷
   rw⁻ 0 (q245 c4) ∷ []) Eq.refl

private
  q246 : Ws → Eqn
  q246 c4 = sE 1144 (lem-sym-bc-at0310243142 c4)

-- box-perm-1324 @0310243142: 1 steps
lem-box-perm-1324-at0310243142 : Ws → ⟪ (ℓ "佨") ⟫ʷ ≈ ⟪ (ℓ "佥") ⟫ʷ
lem-box-perm-1324-at0310243142 c4 = derive (ℓ "佨") (ℓ "佥")
  (rw 0 (q246 c4) ∷ []) Eq.refl

private
  q247 : Ws → Eqn
  q247 c4 = wlE 348 (lit c4)
  q248 : Ws → Eqn
  q248 c4 = wpE 3 c4
  q249 : Ws → Eqn
  q249 c4 = wpE 221 c4

-- Xb-box @0310243142: 18 steps
lem-Xb-box-at0310243142 : Ws → ⟪ (ℓ "並佨並") ⟫ʷ ≈ ⟪ (ℓ "佨二") ⟫ʷ
lem-Xb-box-at0310243142 c4 = derive (ℓ "並佨並") (ℓ "佨二")
  (rw 1 (q221 c4) ∷
   rw⁻ 0 (q230 c4) ∷
   rw 2 (q231 c4) ∷
   rw⁻ 1 (q232 c4) ∷
   rw 4 (q247 c4) ∷
   rw⁻ 8 (q248 c4) ∷
   rw⁻ 7 (q249 c4) ∷
   rw 6 (q236 c4) ∷
   rw⁻ 5 (q249 c4) ∷
   rw 4 (q237 c4) ∷
   rw⁻ 5 (q247 c4) ∷
   rw⁻ 3 (q238 c4) ∷
   rw⁻ 2 (q230 c4) ∷
   rw 3 (q239 c4) ∷
   rw 4 (q240 c4) ∷
   rw⁻ 3 (q232 c4) ∷
   rw⁻ 0 (q221 c4) ∷
   rw⁻ 1 (q241 c4) ∷ []) Eq.refl

private
  q250 : Ws → Eqn
  q250 c4 = sE 1088 (lem-P-box-at0314213240 c4)
  q251 : Ws → Eqn
  q251 c4 = sE 1121 (lem-box-cP-at0314213240 c4)
  q252 : Ws → Eqn
  q252 c4 = sE 353 (lem-box-tQ-at0312203441 c4)

-- pairs @0314213240: 4 steps
lem-pairs-at0314213240 : Ws → ⟪ (ℓ "侅") ⟫ʷ ≈ ⟪ (ℓ "佱") ⟫ʷ
lem-pairs-at0314213240 c4 = derive (ℓ "侅") (ℓ "佱")
  (rw⁻ 0 (q250 c4) ∷
   rw 1 (q251 c4) ∷
   rw 4 (q226 c4) ∷
   rw⁻ 0 (q252 c4) ∷ []) Eq.refl

private
  q253 : Ws → Eqn
  q253 c4 = sE 1148 (lem-sym-bc-at0312203441 c4)

-- box-perm-1324 @0312203441: 1 steps
lem-box-perm-1324-at0312203441 : Ws → ⟪ (ℓ "佱") ⟫ʷ ≈ ⟪ (ℓ "佴") ⟫ʷ
lem-box-perm-1324-at0312203441 c4 = derive (ℓ "佱") (ℓ "佴")
  (rw 0 (q253 c4) ∷ []) Eq.refl

private
  q254 : Ws → Eqn
  q254 c4 = sE 1120 (lem-box-cP-at0312243041 c4)
  q255 : Ws → Eqn
  q255 c4 = wlE 1274 (lit c4)
  q256 : Ws → Eqn
  q256 c4 = wlE 1275 (lit c4)
  q257 : Ws → Eqn
  q257 c4 = eqn (ℓ "亓並") (ℓ "並亓") (c₄ (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) (X))
  q258 : Ws → Eqn
  q258 c4 = wlE 1273 (lit c4)
  q259 : Ws → Eqn
  q259 c4 = wlE 415 (lit c4)
  q260 : Ws → Eqn
  q260 c4 = wpE 366 c4
  q261 : Ws → Eqn
  q261 c4 = wlE 1071 (lit c4)
  q262 : Ws → Eqn
  q262 c4 = wlE 1276 (lit c4)
  q263 : Ws → Eqn
  q263 c4 = wlE 1265 (lit c4)

-- Xb-box @0312243041: 18 steps
lem-Xb-box-at0312243041 : Ws → ⟪ (ℓ "並佴並") ⟫ʷ ≈ ⟪ (ℓ "佴二") ⟫ʷ
lem-Xb-box-at0312243041 c4 = derive (ℓ "並佴並") (ℓ "佴二")
  (rw 1 (q254 c4) ∷
   rw⁻ 0 (q255 c4) ∷
   rw 2 (q256 c4) ∷
   rw⁻ 1 (q257 c4) ∷
   rw 4 (q258 c4) ∷
   rw⁻ 8 (q259 c4) ∷
   rw⁻ 7 (q260 c4) ∷
   rw 6 (q184 c4) ∷
   rw⁻ 5 (q260 c4) ∷
   rw 4 (q185 c4) ∷
   rw⁻ 5 (q258 c4) ∷
   rw⁻ 3 (q261 c4) ∷
   rw⁻ 2 (q255 c4) ∷
   rw 3 (q262 c4) ∷
   rw 4 (q263 c4) ∷
   rw⁻ 3 (q257 c4) ∷
   rw⁻ 0 (q254 c4) ∷
   rw⁻ 1 (q241 c4) ∷ []) Eq.refl

private
  q264 : Ws → Eqn
  q264 c4 = sE 1149 (lem-sym-bc-at0312243041 c4)

-- box-perm-1324 @0312243041: 1 steps
lem-box-perm-1324-at0312243041 : Ws → ⟪ (ℓ "佴") ⟫ʷ ≈ ⟪ (ℓ "佱") ⟫ʷ
lem-box-perm-1324-at0312243041 c4 = derive (ℓ "佴") (ℓ "佱")
  (rw 0 (q264 c4) ∷ []) Eq.refl

private
  q265 : Ws → Eqn
  q265 c4 = sE 1085 (lem-P-box-at0312203441 c4)
  q266 : Ws → Eqn
  q266 c4 = sE 1118 (lem-box-cP-at0312203441 c4)
  q267 : Ws → Eqn
  q267 c4 = sE 355 (lem-box-tQ-at0314213240 c4)

-- pairs @0312203441: 4 steps
lem-pairs-at0312203441 : Ws → ⟪ (ℓ "佱") ⟫ʷ ≈ ⟪ (ℓ "侅") ⟫ʷ
lem-pairs-at0312203441 c4 = derive (ℓ "佱") (ℓ "侅")
  (rw⁻ 0 (q265 c4) ∷
   rw 1 (q266 c4) ∷
   rw 4 (q212 c4) ∷
   rw⁻ 0 (q267 c4) ∷ []) Eq.refl

private
  q268 : Ws → Eqn
  q268 c4 = sE 1155 (lem-sym-bc-at033440 c4)

-- box-perm-1324 @033440: 1 steps
lem-box-perm-1324-at033440 : Ws → ⟪ (ℓ "佭") ⟫ʷ ≈ ⟪ (ℓ "佯") ⟫ʷ
lem-box-perm-1324-at033440 c4 = derive (ℓ "佭") (ℓ "佯")
  (rw 0 (q268 c4) ∷ []) Eq.refl

private
  q269 : Ws → Eqn
  q269 c4 = wlE 1279 (lit c4)
  q270 : Ws → Eqn
  q270 c4 = wlE 1280 (lit c4)
  q271 : Ws → Eqn
  q271 c4 = eqn (ℓ "些並") (ℓ "並些") (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (X))
  q272 : Ws → Eqn
  q272 c4 = wlE 155 (lit c4)
  q273 : Ws → Eqn
  q273 c4 = wpE 261 c4
  q274 : Ws → Eqn
  q274 c4 = wlE 679 (lit c4)
  q275 : Ws → Eqn
  q275 c4 = sE 432 (lem-comm-CSd02-CCZ134 c4)
  q276 : Ws → Eqn
  q276 c4 = sE 431 (lem-comm-CS02-CCZ134 c4)
  q277 : Ws → Eqn
  q277 c4 = wlE 1281 (lit c4)
  q278 : Ws → Eqn
  q278 c4 = wlE 1282 (lit c4)
  q279 : Ws → Eqn
  q279 c4 = wlE 1251 (lit c4)

-- Xb-box @03243240: 18 steps
lem-Xb-box-at03243240 : Ws → ⟪ (ℓ "並佯並") ⟫ʷ ≈ ⟪ (ℓ "佯二") ⟫ʷ
lem-Xb-box-at03243240 c4 = derive (ℓ "並佯並") (ℓ "佯二")
  (rw 1 (q211 c4) ∷
   rw⁻ 0 (q269 c4) ∷
   rw 2 (q270 c4) ∷
   rw⁻ 1 (q271 c4) ∷
   rw 4 (q272 c4) ∷
   rw⁻ 8 (q273 c4) ∷
   rw⁻ 7 (q274 c4) ∷
   rw 6 (q275 c4) ∷
   rw⁻ 5 (q274 c4) ∷
   rw 4 (q276 c4) ∷
   rw⁻ 5 (q272 c4) ∷
   rw⁻ 3 (q277 c4) ∷
   rw⁻ 2 (q269 c4) ∷
   rw 3 (q278 c4) ∷
   rw 4 (q279 c4) ∷
   rw⁻ 3 (q271 c4) ∷
   rw⁻ 0 (q211 c4) ∷
   rw⁻ 1 (q241 c4) ∷ []) Eq.refl

private
  q280 : Ws → Eqn
  q280 c4 = sE 1163 (lem-sym-bc-at3443 c4)

-- box-perm-1324 @3443: 1 steps
lem-box-perm-1324-at3443 : Ws → ⟪ (ℓ "亼") ⟫ʷ ≈ ⟪ (ℓ "仄") ⟫ʷ
lem-box-perm-1324-at3443 c4 = derive (ℓ "亼") (ℓ "仄")
  (rw 0 (q280 c4) ∷ []) Eq.refl

private
  q281 : Ws → Eqn
  q281 c4 = sE 1089 (lem-P-box-at03243240 c4)
  q282 : Ws → Eqn
  q282 c4 = sE 398 (lem-box-tQ-at03122031 c4)

-- pairs @03243240: 4 steps
lem-pairs-at03243240 : Ws → ⟪ (ℓ "佯") ⟫ʷ ≈ ⟪ (ℓ "佰") ⟫ʷ
lem-pairs-at03243240 c4 = derive (ℓ "佯") (ℓ "佰")
  (rw⁻ 0 (q281 c4) ∷
   rw 1 (q211 c4) ∷
   rw 4 (q226 c4) ∷
   rw⁻ 0 (q282 c4) ∷ []) Eq.refl

private
  q283 : Ws → Eqn
  q283 c4 = sE 1135 (lem-pairs-at03102132 c4)
  q284 : Ws → Eqn
  q284 c4 = sE 1075 (lem-sym-ab-at0312243041 c4)
  q285 : Ws → Eqn
  q285 c4 = sE 1152 (lem-sym-bc-at03143041 c4)

-- box-perm-4132 @03102132: 3 steps
lem-box-perm-4132-at03102132 : Ws → ⟪ (ℓ "佤") ⟫ʷ ≈ ⟪ (ℓ "佾") ⟫ʷ
lem-box-perm-4132-at03102132 c4 = derive (ℓ "佤") (ℓ "佾")
  (rw 0 (q283 c4) ∷
   rw 0 (q284 c4) ∷
   rw 0 (q285 c4) ∷ []) Eq.refl

private
  q286 : Ws → Eqn
  q286 c4 = sE 1140 (lem-sym-bc-at02142041 c4)

-- box-perm-1324 @02142041: 1 steps
lem-box-perm-1324-at02142041 : Ws → ⟪ (ℓ "余") ⟫ʷ ≈ ⟪ (ℓ "佢") ⟫ʷ
lem-box-perm-1324-at02142041 c4 = derive (ℓ "余") (ℓ "佢")
  (rw 0 (q286 c4) ∷ []) Eq.refl

private
  q287 : Ws → Eqn
  q287 c4 = sE 1072 (lem-sym-ab-at0214233041 c4)

-- box-perm-3124 @02142041: 2 steps
lem-box-perm-3124-at02142041 : Ws → ⟪ (ℓ "余") ⟫ʷ ≈ ⟪ (ℓ "佋") ⟫ʷ
lem-box-perm-3124-at02142041 c4 = derive (ℓ "余") (ℓ "佋")
  (rw 0 (q286 c4) ∷
   rw 0 (q287 c4) ∷ []) Eq.refl

private
  q288 : Ws → Eqn
  q288 c4 = sE 1150 (lem-sym-bc-at0314203241 c4)
  q289 : Ws → Eqn
  q289 c4 = sE 1077 (lem-sym-ab-at03143041 c4)

-- box-perm-3124 @0314203241: 2 steps
lem-box-perm-3124-at0314203241 : Ws → ⟪ (ℓ "佾") ⟫ʷ ≈ ⟪ (ℓ "佴") ⟫ʷ
lem-box-perm-3124-at0314203241 c4 = derive (ℓ "佾") (ℓ "佴")
  (rw 0 (q288 c4) ∷
   rw 0 (q289 c4) ∷ []) Eq.refl

private
  q290 : Ws → Eqn
  q290 c4 = sE 730 (lem-sym-ab-at0213243041 c4)
  q291 : Ws → Eqn
  q291 c4 = sE 1134 (lem-pairs-at0214233041 c4)
  q292 : Ws → Eqn
  q292 c4 = sE 956 (lem-sym-bc-at0210213443 c4)
  q293 : Ws → Eqn
  q293 c4 = sE 53 (lem-sym-ab-at0210243143 c4)

-- box-perm-2341 @0213243041: 4 steps
lem-box-perm-2341-at0213243041 : Ws → ⟪ (ℓ "佋") ⟫ʷ ≈ ⟪ (ℓ "佔") ⟫ʷ
lem-box-perm-2341-at0213243041 c4 = derive (ℓ "佋") (ℓ "佔")
  (rw 0 (q290 c4) ∷
   rw 0 (q291 c4) ∷
   rw 0 (q292 c4) ∷
   rw 0 (q293 c4) ∷ []) Eq.refl

private
  q294 : Ws → Eqn
  q294 c4 = sE 1029 (lem-sym-ab-at0214203143 c4)
  q295 : Ws → Eqn
  q295 c4 = sE 1014 (lem-sym-bc-at0210243143 c4)
  q296 : Ws → Eqn
  q296 c4 = sE 1132 (lem-pairs-at0210213443 c4)

-- box-perm-4123 @0214203143: 4 steps
lem-box-perm-4123-at0214203143 : Ws → ⟪ (ℓ "佔") ⟫ʷ ≈ ⟪ (ℓ "佋") ⟫ʷ
lem-box-perm-4123-at0214203143 c4 = derive (ℓ "佔") (ℓ "佋")
  (rw 0 (q294 c4) ∷
   rw 0 (q295 c4) ∷
   rw 0 (q296 c4) ∷
   rw 0 (q287 c4) ∷ []) Eq.refl

-- box-perm-2314 @0312243041: 2 steps
lem-box-perm-2314-at0312243041 : Ws → ⟪ (ℓ "佴") ⟫ʷ ≈ ⟪ (ℓ "佾") ⟫ʷ
lem-box-perm-2314-at0312243041 c4 = derive (ℓ "佴") (ℓ "佾")
  (rw 0 (q284 c4) ∷
   rw 0 (q285 c4) ∷ []) Eq.refl

private
  q297 : Ws → Eqn
  q297 c4 = sE 1102 (lem-P-box-at0312243041 c4)
  q298 : Ws → Eqn
  q298 c4 = wlE 443 (lit c4)
  q299 : Ws → Eqn
  q299 c4 = sE 138 (lem-box-tQ-at03102132 c4)

-- pairs @0312243041: 4 steps
lem-pairs-at0312243041 : Ws → ⟪ (ℓ "佴") ⟫ʷ ≈ ⟪ (ℓ "佤") ⟫ʷ
lem-pairs-at0312243041 c4 = derive (ℓ "佴") (ℓ "佤")
  (rw⁻ 0 (q297 c4) ∷
   rw 1 (q254 c4) ∷
   rw 4 (q298 c4) ∷
   rw⁻ 0 (q299 c4) ∷ []) Eq.refl

private
  q300 : Ws → Eqn
  q300 c4 = sE 1097 (lem-P-box-at02102441 c4)
  q301 : Ws → Eqn
  q301 c4 = sE 397 (lem-box-tQ-at02132130 c4)

-- pairs @02102441: 4 steps
lem-pairs-at02102441 : Ws → ⟪ (ℓ "伲") ⟫ʷ ≈ ⟪ (ℓ "佅") ⟫ʷ
lem-pairs-at02102441 c4 = derive (ℓ "伲") (ℓ "佅")
  (rw⁻ 0 (q300 c4) ∷
   rw 1 (q99 c4) ∷
   rw 4 (q71 c4) ∷
   rw⁻ 0 (q301 c4) ∷ []) Eq.refl

private
  q302 : Ws → Eqn
  q302 c4 = sE 1103 (lem-P-box-at03143041 c4)
  q303 : Ws → Eqn
  q303 c4 = sE 1122 (lem-box-cP-at03143041 c4)
  q304 : Ws → Eqn
  q304 c4 = sE 149 (lem-box-tQ-at0310213442 c4)

-- pairs @03143041: 4 steps
lem-pairs-at03143041 : Ws → ⟪ (ℓ "侈") ⟫ʷ ≈ ⟪ (ℓ "佥") ⟫ʷ
lem-pairs-at03143041 c4 = derive (ℓ "侈") (ℓ "佥")
  (rw⁻ 0 (q302 c4) ∷
   rw 1 (q303 c4) ∷
   rw 4 (q298 c4) ∷
   rw⁻ 0 (q304 c4) ∷ []) Eq.refl

private
  q305 : Ws → Eqn
  q305 c4 = sE 1098 (lem-P-box-at02132130 c4)
  q306 : Ws → Eqn
  q306 c4 = sE 1111 (lem-box-cP-at02132130 c4)
  q307 : Ws → Eqn
  q307 c4 = sE 348 (lem-box-tQ-at02102441 c4)

-- pairs @02132130: 4 steps
lem-pairs-at02132130 : Ws → ⟪ (ℓ "佅") ⟫ʷ ≈ ⟪ (ℓ "伲") ⟫ʷ
lem-pairs-at02132130 c4 = derive (ℓ "佅") (ℓ "伲")
  (rw⁻ 0 (q305 c4) ∷
   rw 1 (q306 c4) ∷
   rw 4 (q90 c4) ∷
   rw⁻ 0 (q307 c4) ∷ []) Eq.refl

-- box-perm-1324 @0314203241: 1 steps
lem-box-perm-1324-at0314203241 : Ws → ⟪ (ℓ "佾") ⟫ʷ ≈ ⟪ (ℓ "侈") ⟫ʷ
lem-box-perm-1324-at0314203241 c4 = derive (ℓ "佾") (ℓ "侈")
  (rw 0 (q288 c4) ∷ []) Eq.refl

private
  q308 : Ws → Eqn
  q308 c4 = sE 1031 (lem-sym-ab-at0314203142 c4)
  q309 : Ws → Eqn
  q309 c4 = sE 1136 (lem-pairs-at0310213442 c4)

-- box-perm-4123 @0314203142: 4 steps
lem-box-perm-4123-at0314203142 : Ws → ⟪ (ℓ "佹") ⟫ʷ ≈ ⟪ (ℓ "佴") ⟫ʷ
lem-box-perm-4123-at0314203142 c4 = derive (ℓ "佹") (ℓ "佴")
  (rw 0 (q308 c4) ∷
   rw 0 (q246 c4) ∷
   rw 0 (q309 c4) ∷
   rw 0 (q289 c4) ∷ []) Eq.refl

private
  q310 : Ws → Eqn
  q310 c4 = sE 1133 (lem-pairs-at0213243041 c4)

-- box-perm-2431 @02142041: 3 steps
lem-box-perm-2431-at02142041 : Ws → ⟪ (ℓ "余") ⟫ʷ ≈ ⟪ (ℓ "伭") ⟫ʷ
lem-box-perm-2431-at02142041 c4 = derive (ℓ "余") (ℓ "伭")
  (rw 0 (q286 c4) ∷
   rw 0 (q287 c4) ∷
   rw 0 (q310 c4) ∷ []) Eq.refl

private
  q311 : Ws → Eqn
  q311 c4 = sE 1099 (lem-P-box-at0310243241 c4)
  q312 : Ws → Eqn
  q312 c4 = sE 399 (lem-box-tQ-at03122130 c4)

-- pairs @0310243241: 4 steps
lem-pairs-at0310243241 : Ws → ⟪ (ℓ "佩") ⟫ʷ ≈ ⟪ (ℓ "佲") ⟫ʷ
lem-pairs-at0310243241 c4 = derive (ℓ "佩") (ℓ "佲")
  (rw⁻ 0 (q311 c4) ∷
   rw 1 (q229 c4) ∷
   rw 4 (q209 c4) ∷
   rw⁻ 0 (q312 c4) ∷ []) Eq.refl

private
  q313 : Ws → Eqn
  q313 c4 = sE 1131 (lem-pairs-at021021 c4)

-- box-perm-1243 @021021: 3 steps
lem-box-perm-1243-at021021 : Ws → ⟪ (ℓ "伭") ⟫ʷ ≈ ⟪ (ℓ "伮") ⟫ʷ
lem-box-perm-1243-at021021 c4 = derive (ℓ "伭") (ℓ "伮")
  (rw 0 (q313 c4) ∷
   rw 0 (q290 c4) ∷
   rw 0 (q291 c4) ∷ []) Eq.refl

-- box-perm-1243 @0210213443: 3 steps
lem-box-perm-1243-at0210213443 : Ws → ⟪ (ℓ "伮") ⟫ʷ ≈ ⟪ (ℓ "伭") ⟫ʷ
lem-box-perm-1243-at0210213443 c4 = derive (ℓ "伮") (ℓ "伭")
  (rw 0 (q296 c4) ∷
   rw 0 (q287 c4) ∷
   rw 0 (q310 c4) ∷ []) Eq.refl

private
  q314 : Ws → Eqn
  q314 c4 = sE 1101 (lem-P-box-at03122130 c4)
  q315 : Ws → Eqn
  q315 c4 = sE 1119 (lem-box-cP-at03122130 c4)
  q316 : Ws → Eqn
  q316 c4 = sE 350 (lem-box-tQ-at0310243241 c4)

-- pairs @03122130: 4 steps
lem-pairs-at03122130 : Ws → ⟪ (ℓ "佲") ⟫ʷ ≈ ⟪ (ℓ "佩") ⟫ʷ
lem-pairs-at03122130 c4 = derive (ℓ "佲") (ℓ "佩")
  (rw⁻ 0 (q314 c4) ∷
   rw 1 (q315 c4) ∷
   rw 4 (q218 c4) ∷
   rw⁻ 0 (q316 c4) ∷ []) Eq.refl

private
  q317 : Ws → Eqn
  q317 c4 = sE 892 (lem-sym-bc-at0214233041 c4)

-- box-perm-4132 @021021: 3 steps
lem-box-perm-4132-at021021 : Ws → ⟪ (ℓ "伭") ⟫ʷ ≈ ⟪ (ℓ "余") ⟫ʷ
lem-box-perm-4132-at021021 c4 = derive (ℓ "伭") (ℓ "余")
  (rw 0 (q313 c4) ∷
   rw 0 (q290 c4) ∷
   rw 0 (q317 c4) ∷ []) Eq.refl

private
  q318 : Ws → Eqn
  q318 c4 = sE 349 (lem-box-tQ-at02142041 c4)
  q319 : Ws → Eqn
  q319 c4 = sE 1164 (lem-box-cP-at02142041 c4)
  q320 : Ws → Eqn
  q320 c4 = sE 1106 (lem-t-cP-at02142041 c4)

-- box2 @02142041: 11 steps
lem-box2-at02142041 : Ws → ⟪ (ℓ "余余") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at02142041 c4 = derive (ℓ "余余") []
  (rw 0 (q318 c4) ∷
   rw 4 (q319 c4) ∷
   rw⁻ 4 (q90 c4) ∷
   rw 5 (q320 c4) ∷
   rw⁻ 5 (q319 c4) ∷
   rw 5 (q318 c4) ∷
   rw 4 (q90 c4) ∷
   rw 3 (q223 c4) ∷
   rw 2 (q90 c4) ∷
   rw 1 (q223 c4) ∷
   rw 0 (q90 c4) ∷ []) Eq.refl

private
  q321 : Ws → Eqn
  q321 c4 = sE 400 (lem-box-tQ-at0314203241 c4)
  q322 : Ws → Eqn
  q322 c4 = sE 1165 (lem-box-cP-at0314203241 c4)
  q323 : Ws → Eqn
  q323 c4 = sE 1107 (lem-t-cP-at0314203241 c4)

-- box2 @0314203241: 11 steps
lem-box2-at0314203241 : Ws → ⟪ (ℓ "佾佾") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0314203241 c4 = derive (ℓ "佾佾") []
  (rw 0 (q321 c4) ∷
   rw 4 (q322 c4) ∷
   rw⁻ 4 (q218 c4) ∷
   rw 5 (q323 c4) ∷
   rw⁻ 5 (q322 c4) ∷
   rw 5 (q321 c4) ∷
   rw 4 (q218 c4) ∷
   rw 3 (q223 c4) ∷
   rw 2 (q218 c4) ∷
   rw 1 (q223 c4) ∷
   rw 0 (q218 c4) ∷ []) Eq.refl

private
  q324 : Ws → Eqn
  q324 c4 = sE 1081 (lem-sym-ab-at02132130 c4)
  q325 : Ws → Eqn
  q325 c4 = sE 1141 (lem-sym-bc-at022330 c4)

-- box-perm-2314 @02132130: 2 steps
lem-box-perm-2314-at02132130 : Ws → ⟪ (ℓ "佅") ⟫ʷ ≈ ⟪ (ℓ "伳") ⟫ʷ
lem-box-perm-2314-at02132130 c4 = derive (ℓ "佅") (ℓ "伳")
  (rw 0 (q324 c4) ∷
   rw 0 (q325 c4) ∷ []) Eq.refl

private
  q326 : Ws → Eqn
  q326 c4 = sE 1074 (lem-sym-ab-at03122130 c4)
  q327 : Ws → Eqn
  q327 c4 = sE 1015 (lem-sym-bc-at0330 c4)

-- box-perm-2314 @03122130: 2 steps
lem-box-perm-2314-at03122130 : Ws → ⟪ (ℓ "佲") ⟫ʷ ≈ ⟪ (ℓ "佪") ⟫ʷ
lem-box-perm-2314-at03122130 c4 = derive (ℓ "佲") (ℓ "佪")
  (rw 0 (q326 c4) ∷
   rw 0 (q327 c4) ∷ []) Eq.refl

private
  q328 : Ws → Eqn
  q328 c4 = sE 1073 (lem-sym-ab-at03122031 c4)
  q329 : Ws → Eqn
  q329 c4 = sE 1146 (lem-sym-bc-at031031 c4)
  q330 : Ws → Eqn
  q330 c4 = sE 40 (lem-sym-ab-at03102132 c4)

-- box-perm-3214 @03122031: 3 steps
lem-box-perm-3214-at03122031 : Ws → ⟪ (ℓ "佰") ⟫ʷ ≈ ⟪ (ℓ "佪") ⟫ʷ
lem-box-perm-3214-at03122031 c4 = derive (ℓ "佰") (ℓ "佪")
  (rw 0 (q328 c4) ∷
   rw 0 (q329 c4) ∷
   rw 0 (q330 c4) ∷ []) Eq.refl

private
  q331 : Ws → Eqn
  q331 c4 = sE 1100 (lem-P-box-at031031 c4)
  q332 : Ws → Eqn
  q332 c4 = sE 1116 (lem-box-cP-at031031 c4)
  q333 : Ws → Eqn
  q333 c4 = sE 401 (lem-box-tQ-at03243042 c4)

-- pairs @031031: 4 steps
lem-pairs-at031031 : Ws → ⟪ (ℓ "佦") ⟫ʷ ≈ ⟪ (ℓ "佮") ⟫ʷ
lem-pairs-at031031 c4 = derive (ℓ "佦") (ℓ "佮")
  (rw⁻ 0 (q331 c4) ∷
   rw 1 (q332 c4) ∷
   rw 4 (q212 c4) ∷
   rw⁻ 0 (q333 c4) ∷ []) Eq.refl

private
  q334 : Ws → Eqn
  q334 c4 = sE 1169 (lem-sym-bc-at142142 c4)

-- box-perm-1324 @142142: 1 steps
lem-box-perm-1324-at142142 : Ws → ⟪ (ℓ "企") ⟫ʷ ≈ ⟪ (ℓ "伋") ⟫ʷ
lem-box-perm-1324-at142142 c4 = derive (ℓ "企") (ℓ "伋")
  (rw 0 (q334 c4) ∷ []) Eq.refl

private
  q335 : Ws → Eqn
  q335 c4 = sE 1070 (lem-sym-ab-at14233142 c4)

-- box-perm-3124 @142142: 2 steps
lem-box-perm-3124-at142142 : Ws → ⟪ (ℓ "企") ⟫ʷ ≈ ⟪ (ℓ "仳") ⟫ʷ
lem-box-perm-3124-at142142 c4 = derive (ℓ "企") (ℓ "仳")
  (rw 0 (q334 c4) ∷
   rw 0 (q335 c4) ∷ []) Eq.refl

private
  q336 : Ws → Eqn
  q336 c4 = sE 895 (lem-sym-ab-at13243142 c4)
  q337 : Ws → Eqn
  q337 c4 = sE 1137 (lem-pairs-at14233142 c4)

-- box-perm-2341 @13243142: 4 steps
lem-box-perm-2341-at13243142 : Ws → ⟪ (ℓ "仳") ⟫ʷ ≈ ⟪ (ℓ "仼") ⟫ʷ
lem-box-perm-2341-at13243142 c4 = derive (ℓ "仳") (ℓ "仼")
  (rw 0 (q336 c4) ∷
   rw 0 (q337 c4) ∷
   rw 0 (q280 c4) ∷
   rw 0 (q144 c4) ∷ []) Eq.refl

private
  q338 : Ws → Eqn
  q338 c4 = sE 1104 (lem-P-box-at03243042 c4)
  q339 : Ws → Eqn
  q339 c4 = sE 1166 (lem-box-cP-at03243042 c4)
  q340 : Ws → Eqn
  q340 c4 = sE 351 (lem-box-tQ-at031031 c4)

-- pairs @03243042: 4 steps
lem-pairs-at03243042 : Ws → ⟪ (ℓ "佮") ⟫ʷ ≈ ⟪ (ℓ "佦") ⟫ʷ
lem-pairs-at03243042 c4 = derive (ℓ "佮") (ℓ "佦")
  (rw⁻ 0 (q338 c4) ∷
   rw 1 (q339 c4) ∷
   rw 4 (q226 c4) ∷
   rw⁻ 0 (q340 c4) ∷ []) Eq.refl

private
  q341 : Ws → Eqn
  q341 c4 = sE 1105 (lem-P-box-at2442 c4)
  q342 : Ws → Eqn
  q342 c4 = wlE 203 (lit c4)
  q343 : Ws → Eqn
  q343 c4 = sE 260 (lem-box-tQ-at1331 c4)

-- pairs @2442: 4 steps
lem-pairs-at2442 : Ws → ⟪ (ℓ "仆") ⟫ʷ ≈ ⟪ (ℓ "仭") ⟫ʷ
lem-pairs-at2442 c4 = derive (ℓ "仆") (ℓ "仭")
  (rw⁻ 0 (q341 c4) ∷
   rw 1 (q113 c4) ∷
   rw 4 (q342 c4) ∷
   rw⁻ 0 (q343 c4) ∷ []) Eq.refl

private
  q344 : Ws → Eqn
  q344 c4 = sE 1080 (lem-sym-ab-at02132031 c4)
  q345 : Ws → Eqn
  q345 c4 = sE 1168 (lem-sym-bc-at02102331 c4)

-- box-perm-2314 @02132031: 2 steps
lem-box-perm-2314-at02132031 : Ws → ⟪ (ℓ "似") ⟫ʷ ≈ ⟪ (ℓ "伭") ⟫ʷ
lem-box-perm-2314-at02132031 c4 = derive (ℓ "似") (ℓ "伭")
  (rw 0 (q344 c4) ∷
   rw 0 (q345 c4) ∷ []) Eq.refl

private
  q346 : Ws → Eqn
  q346 c4 = sE 404 (lem-box-tQ-at142142 c4)
  q347 : Ws → Eqn
  q347 c4 = sE 1167 (lem-box-cP-at142142 c4)
  q348 : Ws → Eqn
  q348 c4 = wpE 51 c4
  q349 : Ws → Eqn
  q349 c4 = sE 1109 (lem-t-cP-at142142 c4)

-- box2 @142142: 11 steps
lem-box2-at142142 : Ws → ⟪ (ℓ "企企") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at142142 c4 = derive (ℓ "企企") []
  (rw 0 (q346 c4) ∷
   rw 4 (q347 c4) ∷
   rw⁻ 4 (q348 c4) ∷
   rw 5 (q349 c4) ∷
   rw⁻ 5 (q347 c4) ∷
   rw 5 (q346 c4) ∷
   rw 4 (q348 c4) ∷
   rw 3 (q214 c4) ∷
   rw 2 (q348 c4) ∷
   rw 1 (q214 c4) ∷
   rw 0 (q348 c4) ∷ []) Eq.refl

private
  q350 : Ws → Eqn
  q350 c4 = sE 1010 (lem-pairs-at13243142 c4)

-- box-perm-2431 @142142: 3 steps
lem-box-perm-2431-at142142 : Ws → ⟪ (ℓ "企") ⟫ʷ ≈ ⟪ (ℓ "亹") ⟫ʷ
lem-box-perm-2431-at142142 c4 = derive (ℓ "企") (ℓ "亹")
  (rw 0 (q334 c4) ∷
   rw 0 (q335 c4) ∷
   rw 0 (q350 c4) ∷ []) Eq.refl

private
  q351 : Ws → Eqn
  q351 c4 = sE 1108 (lem-t-cP-at033440 c4)
  q352 : Ws → Eqn
  q352 c4 = wpE 7 c4

-- box2 @033440: 11 steps
lem-box2-at033440 : Ws → ⟪ (ℓ "佭佭") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at033440 c4 = derive (ℓ "佭佭") []
  (rw 0 (q210 c4) ∷
   rw 4 (q217 c4) ∷
   rw⁻ 4 (q209 c4) ∷
   rw 5 (q351 c4) ∷
   rw⁻ 5 (q217 c4) ∷
   rw 5 (q210 c4) ∷
   rw 4 (q209 c4) ∷
   rw 3 (q352 c4) ∷
   rw 2 (q209 c4) ∷
   rw 1 (q352 c4) ∷
   rw 0 (q209 c4) ∷ []) Eq.refl
