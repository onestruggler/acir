{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The lemmas of Five/D that F4 uses, instantiated
--
-- Each derivation module takes the lemmas of the others that it uses
-- as a list (DSig); here every lemma that one uses, or that the
-- consumer does, is the lemma of its module applied to its list, in
-- dependency order.  Written by `scratchpad/four/di.py`.
------------------------------------------------------------------------

module Examples.Groups.Clifford+CS.Five.DAll.F4 where

open import Examples.Groups.Clifford+CS.Five.DSig
import Examples.Groups.Clifford+CS.Five.D.D001 as D001
import Examples.Groups.Clifford+CS.Five.D.D002 as D002
import Examples.Groups.Clifford+CS.Five.D.D004 as D004
import Examples.Groups.Clifford+CS.Five.D.D003 as D003
import Examples.Groups.Clifford+CS.Five.D.D005 as D005
import Examples.Groups.Clifford+CS.Five.D.D007 as D007
import Examples.Groups.Clifford+CS.Five.D.D006 as D006
import Examples.Groups.Clifford+CS.Five.D.D009 as D009
import Examples.Groups.Clifford+CS.Five.D.D010 as D010
import Examples.Groups.Clifford+CS.Five.D.D011 as D011
import Examples.Groups.Clifford+CS.Five.D.D008 as D008
import Examples.Groups.Clifford+CS.Five.D.D012 as D012
import Examples.Groups.Clifford+CS.Five.D.D014 as D014
import Examples.Groups.Clifford+CS.Five.D.D013 as D013
import Examples.Groups.Clifford+CS.Five.D.D015 as D015
import Examples.Groups.Clifford+CS.Five.D.D016 as D016
import Examples.Groups.Clifford+CS.Five.D.D018 as D018
import Examples.Groups.Clifford+CS.Five.D.D019 as D019
import Examples.Groups.Clifford+CS.Five.D.D020 as D020
import Examples.Groups.Clifford+CS.Five.D.D025 as D025
import Examples.Groups.Clifford+CS.Five.D.D037 as D037
import Examples.Groups.Clifford+CS.Five.D.D017 as D017
import Examples.Groups.Clifford+CS.Five.D.D021 as D021
import Examples.Groups.Clifford+CS.Five.D.D026 as D026
import Examples.Groups.Clifford+CS.Five.D.D038 as D038
import Examples.Groups.Clifford+CS.Five.D.D027 as D027
import Examples.Groups.Clifford+CS.Five.D.D039 as D039
import Examples.Groups.Clifford+CS.Five.D.D067 as D067
import Examples.Groups.Clifford+CS.Five.D.D028 as D028
import Examples.Groups.Clifford+CS.Five.D.D040 as D040
import Examples.Groups.Clifford+CS.Five.D.D068 as D068
import Examples.Groups.Clifford+CS.Five.D.D042 as D042
import Examples.Groups.Clifford+CS.Five.D.D030 as D030
import Examples.Groups.Clifford+CS.Five.D.D044 as D044
import Examples.Groups.Clifford+CS.Five.D.D070 as D070
import Examples.Groups.Clifford+CS.Five.D.D031 as D031
import Examples.Groups.Clifford+CS.Five.D.D045 as D045
import Examples.Groups.Clifford+CS.Five.D.D043 as D043
import Examples.Groups.Clifford+CS.Five.D.D022 as D022
import Examples.Groups.Clifford+CS.Five.D.D023 as D023
import Examples.Groups.Clifford+CS.Five.D.D032 as D032
import Examples.Groups.Clifford+CS.Five.D.D046 as D046
import Examples.Groups.Clifford+CS.Five.D.D071 as D071
import Examples.Groups.Clifford+CS.Five.D.D147 as D147
import Examples.Groups.Clifford+CS.Five.D.D189 as D189
import Examples.Groups.Clifford+CS.Five.D.D204 as D204

lem-sym-ab : _
lem-sym-ab = D001.lem-sym-ab
lem-cQ-at13243142 : _
lem-cQ-at13243142 = D001.lem-cQ-at13243142
lem-cQ-at13243241 : _
lem-cQ-at13243241 = D001.lem-cQ-at13243241
lem-sym-ab-at2332 : _
lem-sym-ab-at2332 = D001.lem-sym-ab-at2332
lem-sym-ab-at13243142 : _
lem-sym-ab-at13243142 = D001.lem-sym-ab-at13243142
lem-sym-ab-at122331 : _
lem-sym-ab-at122331 = D001.lem-sym-ab-at122331
lem-sym-ab-at13243241 : _
lem-sym-ab-at13243241 = D001.lem-sym-ab-at13243241
lem-sym-ab-at12243143 : _
lem-sym-ab-at12243143 = D001.lem-sym-ab-at12243143
lem-cQ-at14233142 : _
lem-cQ-at14233142 = D001.lem-cQ-at14233142
lem-sym-ab-at13213442 : _
lem-sym-ab-at13213442 = D001.lem-sym-ab-at13213442
lem-sym-ab-at243243 : _
lem-sym-ab-at243243 = D001.lem-sym-ab-at243243
lem-sym-ab-at133441 : _
lem-sym-ab-at133441 = D001.lem-sym-ab-at133441
lem-sym-ab-at12233441 : _
lem-sym-ab-at12233441 = D001.lem-sym-ab-at12233441
lem-sym-ab-at1221 : _
lem-sym-ab-at1221 = D001.lem-sym-ab-at1221
lem-cQ-at021021 : _
lem-cQ-at021021 = D001.lem-cQ-at021021
lem-sym-ab-at233442 : _
lem-sym-ab-at233442 = D001.lem-sym-ab-at233442
lem-cQ-at03102132 : _
lem-cQ-at03102132 = D001.lem-cQ-at03102132
lem-sym-ab-at14233142 : _
lem-sym-ab-at14233142 = D001.lem-sym-ab-at14233142
lem-cQ-at0410213243 : _
lem-cQ-at0410213243 = D001.lem-cQ-at0410213243
lem-cQ-at04203243 : _
lem-cQ-at04203243 = D001.lem-cQ-at04203243
lem-sym-ab-at04203243 : _
lem-sym-ab-at04203243 = D001.lem-sym-ab-at04203243
lem-sym-ab-at0310243142 : _
lem-sym-ab-at0310243142 = D001.lem-sym-ab-at0310243142
lem-sym-ab-at0314203142 : _
lem-sym-ab-at0314203142 = D001.lem-sym-ab-at0314203142
lem-sym-ab-at0410213243 : _
lem-sym-ab-at0410213243 = D001.lem-sym-ab-at0410213243
lem-sym-ab-at03102132 : _
lem-sym-ab-at03102132 = D001.lem-sym-ab-at03102132
lem-cQ-at032032 : _
lem-cQ-at032032 = D001.lem-cQ-at032032
lem-sym-ab-at032032 : _
lem-sym-ab-at032032 = D001.lem-sym-ab-at032032
lem-nat-S : _
lem-nat-S = D001.lem-nat-S
lem-F4-I-I : _
lem-F4-I-I = D001.lem-F4-I-I
lem-F4-I-S0 : _
lem-F4-I-S0 = D001.lem-F4-I-S0
lem-F4-I-S1 : _
lem-F4-I-S1 = D001.lem-F4-I-S1
lem-F4-I-S2 : _
lem-F4-I-S2 = D001.lem-F4-I-S2
lem-F4-I-S3 : _
lem-F4-I-S3 = D001.lem-F4-I-S3
lem-F4-I-K0 : _
lem-F4-I-K0 = D001.lem-F4-I-K0
lem-F4-I-K1 : _
lem-F4-I-K1 = D001.lem-F4-I-K1
lem-F4-I-K2 : _
lem-F4-I-K2 = D001.lem-F4-I-K2
lem-F4-I-K3 : _
lem-F4-I-K3 = D001.lem-F4-I-K3
lem-F4-S0-I : _
lem-F4-S0-I = D001.lem-F4-S0-I
lem-F4-S0-S0 : _
lem-F4-S0-S0 = D001.lem-F4-S0-S0
lem-F4-S0-S1 : _
lem-F4-S0-S1 = D001.lem-F4-S0-S1
lem-F4-S0-S2 : _
lem-F4-S0-S2 = D001.lem-F4-S0-S2
lem-F4-S0-S3 : _
lem-F4-S0-S3 = D001.lem-F4-S0-S3
lem-F4-S0-K0 : _
lem-F4-S0-K0 = D001.lem-F4-S0-K0
lem-F4-S0-K1 : _
lem-F4-S0-K1 = D001.lem-F4-S0-K1
lem-F4-S0-K2 : _
lem-F4-S0-K2 = D001.lem-F4-S0-K2
lem-F4-S0-K3 : _
lem-F4-S0-K3 = D001.lem-F4-S0-K3
lem-F4-S1-I : _
lem-F4-S1-I = D001.lem-F4-S1-I
lem-F4-S1-S0 : _
lem-F4-S1-S0 = D001.lem-F4-S1-S0
lem-F4-S1-S1 : _
lem-F4-S1-S1 = D001.lem-F4-S1-S1
lem-F4-S1-S2 : _
lem-F4-S1-S2 = D001.lem-F4-S1-S2
lem-F4-S1-S3 : _
lem-F4-S1-S3 = D001.lem-F4-S1-S3
lem-F4-S1-K0 : _
lem-F4-S1-K0 = D001.lem-F4-S1-K0
lem-F4-S1-K1 : _
lem-F4-S1-K1 = D001.lem-F4-S1-K1
lem-F4-S1-K2 : _
lem-F4-S1-K2 = D001.lem-F4-S1-K2
lem-F4-S1-K3 : _
lem-F4-S1-K3 = D001.lem-F4-S1-K3
lem-F4-S2-I : _
lem-F4-S2-I = D001.lem-F4-S2-I
lem-F4-S2-S0 : _
lem-F4-S2-S0 = D001.lem-F4-S2-S0
lem-F4-S2-S1 : _
lem-F4-S2-S1 = D001.lem-F4-S2-S1
lem-F4-S2-S2 : _
lem-F4-S2-S2 = D001.lem-F4-S2-S2
lem-F4-S2-S3 : _
lem-F4-S2-S3 = D001.lem-F4-S2-S3
lem-F4-S2-K0 : _
lem-F4-S2-K0 = D001.lem-F4-S2-K0
lem-F4-S2-K1 : _
lem-F4-S2-K1 = D001.lem-F4-S2-K1
lem-F4-S2-K2 : _
lem-F4-S2-K2 = D001.lem-F4-S2-K2
lem-F4-S2-K3 : _
lem-F4-S2-K3 = D001.lem-F4-S2-K3
lem-F4-S3-I : _
lem-F4-S3-I = D001.lem-F4-S3-I
lem-F4-S3-S0 : _
lem-F4-S3-S0 = D001.lem-F4-S3-S0
lem-F4-S3-S1 : _
lem-F4-S3-S1 = D001.lem-F4-S3-S1
lem-F4-S3-S2 : _
lem-F4-S3-S2 = D001.lem-F4-S3-S2
lem-F4-S3-S3 : _
lem-F4-S3-S3 = D001.lem-F4-S3-S3
lem-F4-S3-K0 : _
lem-F4-S3-K0 = D001.lem-F4-S3-K0
lem-F4-S3-K1 : _
lem-F4-S3-K1 = D001.lem-F4-S3-K1
lem-F4-S3-K2 : _
lem-F4-S3-K2 = D001.lem-F4-S3-K2
lem-F4-S3-K3 : _
lem-F4-S3-K3 = D001.lem-F4-S3-K3
lem-F4-K0-I : _
lem-F4-K0-I = D001.lem-F4-K0-I
lem-F4-K0-S0 : _
lem-F4-K0-S0 = D001.lem-F4-K0-S0
lem-F4-K0-S1 : _
lem-F4-K0-S1 = D001.lem-F4-K0-S1
lem-F4-K0-S2 : _
lem-F4-K0-S2 = D001.lem-F4-K0-S2
lem-F4-K0-S3 : _
lem-F4-K0-S3 = D001.lem-F4-K0-S3
lem-F4-K0-K0 : _
lem-F4-K0-K0 = D001.lem-F4-K0-K0
lem-F4-K0-K1 : _
lem-F4-K0-K1 = D001.lem-F4-K0-K1
lem-F4-K0-K2 : _
lem-F4-K0-K2 = D001.lem-F4-K0-K2
lem-F4-K0-K3 : _
lem-F4-K0-K3 = D001.lem-F4-K0-K3
lem-F4-K1-I : _
lem-F4-K1-I = D001.lem-F4-K1-I
lem-F4-K1-S0 : _
lem-F4-K1-S0 = D001.lem-F4-K1-S0
lem-F4-K1-S1 : _
lem-F4-K1-S1 = D001.lem-F4-K1-S1
lem-F4-K1-S2 : _
lem-F4-K1-S2 = D001.lem-F4-K1-S2
lem-F4-K1-S3 : _
lem-F4-K1-S3 = D001.lem-F4-K1-S3
lem-F4-K1-K0 : _
lem-F4-K1-K0 = D001.lem-F4-K1-K0
lem-F4-K1-K1 : _
lem-F4-K1-K1 = D001.lem-F4-K1-K1
lem-F4-K1-K2 : _
lem-F4-K1-K2 = D001.lem-F4-K1-K2
lem-F4-K1-K3 : _
lem-F4-K1-K3 = D001.lem-F4-K1-K3
lem-sym-ab-at0210243143 : _
lem-sym-ab-at0210243143 = D001.lem-sym-ab-at0210243143
lem-nat-SWbc-at0214203143 : _
lem-nat-SWbc-at0214203143 = D001.lem-nat-SWbc-at0214203143
lem-nat-SWbc-at122441 : _
lem-nat-SWbc-at122441 = D001.lem-nat-SWbc-at122441
lem-F4-K2-I : _
lem-F4-K2-I = D001.lem-F4-K2-I
lem-F4-K2-S0 : _
lem-F4-K2-S0 = D001.lem-F4-K2-S0
lem-F4-K2-S1 : _
lem-F4-K2-S1 = D001.lem-F4-K2-S1
lem-F4-K2-S2 : _
lem-F4-K2-S2 = D001.lem-F4-K2-S2
lem-F4-K2-S3 : _
lem-F4-K2-S3 = D001.lem-F4-K2-S3
lem-F4-K2-K0 : _
lem-F4-K2-K0 = D001.lem-F4-K2-K0
lem-F4-K2-K1 : _
lem-F4-K2-K1 = D001.lem-F4-K2-K1
lem-F4-K2-K2 : _
lem-F4-K2-K2 = D001.lem-F4-K2-K2
lem-F4-K2-K3 : _
lem-F4-K2-K3 = D001.lem-F4-K2-K3
lem-nat-SWbc-at14213243 : _
lem-nat-SWbc-at14213243 = D001.lem-nat-SWbc-at14213243
lem-F4-K3-I : _
lem-F4-K3-I = D001.lem-F4-K3-I
lem-F4-K3-S0 : _
lem-F4-K3-S0 = D001.lem-F4-K3-S0
lem-F4-K3-S1 : _
lem-F4-K3-S1 = D001.lem-F4-K3-S1
lem-F4-K3-S2 : _
lem-F4-K3-S2 = D001.lem-F4-K3-S2
lem-F4-K3-S3 : _
lem-F4-K3-S3 = D001.lem-F4-K3-S3
lem-F4-K3-K0 : _
lem-F4-K3-K0 = D001.lem-F4-K3-K0
lem-F4-K3-K1 : _
lem-F4-K3-K1 = D001.lem-F4-K3-K1
lem-F4-K3-K2 : _
lem-F4-K3-K2 = D001.lem-F4-K3-K2
lem-F4-K3-K3 : _
lem-F4-K3-K3 = D001.lem-F4-K3-K3
lem-cQ-at0210213443 : _
lem-cQ-at0210213443 = D001.lem-cQ-at0210213443
lem-sym-ab-at122441 : _
lem-sym-ab-at122441 = D001.lem-sym-ab-at122441
lem-cQ-at14233241 : _
lem-cQ-at14233241 = D001.lem-cQ-at14233241
lem-nat-SWbc-at0314213042 : _
lem-nat-SWbc-at0314213042 = D001.lem-nat-SWbc-at0314213042
lem-sym-ab-at0210233441 : _
lem-sym-ab-at0210233441 = D001.lem-sym-ab-at0210233441
lem-sym-ab-at0213203441 : _
lem-sym-ab-at0213203441 = D001.lem-sym-ab-at0213203441
lem-nat-SWbc-at0314203142 : _
lem-nat-SWbc-at0314203142 = D001.lem-nat-SWbc-at0314203142
lem-nat-SWbc-at0214213043 : _
lem-nat-SWbc-at0214213043 = D001.lem-nat-SWbc-at0214213043
lem-sym-ab-at0214203143 : _
lem-sym-ab-at0214203143 = D001.lem-sym-ab-at0214203143
lem-nat-S-at14213243 : _
lem-nat-S-at14213243 = D001.lem-nat-S-at14213243
lem-nat-SWbc-at1331 : _
lem-nat-SWbc-at1331 = D001.lem-nat-SWbc-at1331
lem-sym-ab-at0312213440 : _
lem-sym-ab-at0312213440 = D001.lem-sym-ab-at0312213440
lem-sym-ab-at033440 : _
lem-sym-ab-at033440 = D001.lem-sym-ab-at033440
lem-nat-SWbc-at132132 : _
lem-nat-SWbc-at132132 = D001.lem-nat-SWbc-at132132
lem-sym-ab-at1331 : _
lem-sym-ab-at1331 = D002.lem-sym-ab-at1331
lem-sym-ab-at0220 : _
lem-sym-ab-at0220 = D002.lem-sym-ab-at0220
lem-sym-ab-at14233241 : _
lem-sym-ab-at14233241 = D002.lem-sym-ab-at14233241
lem-sym-ab-at021021 : _
lem-sym-ab-at021021 = D002.lem-sym-ab-at021021
lem-cQ-at0220 : _
lem-cQ-at0220 = D002.lem-cQ-at0220
lem-cQ-at0213243140 : _
lem-cQ-at0213243140 = D002.lem-cQ-at0213243140
lem-sym-ab-at0213213440 : _
lem-sym-ab-at0213213440 = D002.lem-sym-ab-at0213213440
lem-sym-ab-at02233440 : _
lem-sym-ab-at02233440 = D002.lem-sym-ab-at02233440
lem-nat-SWbc-at12233441 : _
lem-nat-SWbc-at12233441 = D002.lem-nat-SWbc-at12233441
lem-sym-ab-at14213243 : _
lem-sym-ab-at14213243 = D002.lem-sym-ab-at14213243
lem-sym-ab-at132132 : _
lem-sym-ab-at132132 = D002.lem-sym-ab-at132132
lem-F2-I-S0 : _
lem-F2-I-S0 = D002.lem-F2-I-S0
lem-F2-I-S1 : _
lem-F2-I-S1 = D002.lem-F2-I-S1
lem-F2-I-S2 : _
lem-F2-I-S2 = D002.lem-F2-I-S2
lem-F2-I-S3 : _
lem-F2-I-S3 = D002.lem-F2-I-S3
lem-F2-I-K0 : _
lem-F2-I-K0 = D002.lem-F2-I-K0
lem-F2-I-K1 : _
lem-F2-I-K1 = D002.lem-F2-I-K1
lem-F2-I-K2 : _
lem-F2-I-K2 = D002.lem-F2-I-K2
lem-F2-I-K3 : _
lem-F2-I-K3 = D002.lem-F2-I-K3
lem-F2-S0-S1 : _
lem-F2-S0-S1 = D002.lem-F2-S0-S1
lem-F2-S0-S2 : _
lem-F2-S0-S2 = D002.lem-F2-S0-S2
lem-F2-S0-S3 : _
lem-F2-S0-S3 = D002.lem-F2-S0-S3
lem-F2-S0-K1 : _
lem-F2-S0-K1 = D002.lem-F2-S0-K1
lem-F2-S0-K2 : _
lem-F2-S0-K2 = D002.lem-F2-S0-K2
lem-F2-S0-K3 : _
lem-F2-S0-K3 = D002.lem-F2-S0-K3
lem-F2-S1-S2 : _
lem-F2-S1-S2 = D002.lem-F2-S1-S2
lem-F2-S1-S3 : _
lem-F2-S1-S3 = D002.lem-F2-S1-S3
lem-F2-S1-K0 : _
lem-F2-S1-K0 = D002.lem-F2-S1-K0
lem-F2-S1-K2 : _
lem-F2-S1-K2 = D002.lem-F2-S1-K2
lem-F2-S1-K3 : _
lem-F2-S1-K3 = D002.lem-F2-S1-K3
lem-F2-S2-S3 : _
lem-F2-S2-S3 = D002.lem-F2-S2-S3
lem-F2-S2-K0 : _
lem-F2-S2-K0 = D002.lem-F2-S2-K0
lem-F2-S2-K1 : _
lem-F2-S2-K1 = D002.lem-F2-S2-K1
lem-F2-S2-K3 : _
lem-F2-S2-K3 = D002.lem-F2-S2-K3
lem-F2-S3-K0 : _
lem-F2-S3-K0 = D002.lem-F2-S3-K0
lem-F2-S3-K1 : _
lem-F2-S3-K1 = D002.lem-F2-S3-K1
lem-F2-S3-K2 : _
lem-F2-S3-K2 = D002.lem-F2-S3-K2
lem-F2-K0-K1 : _
lem-F2-K0-K1 = D002.lem-F2-K0-K1
lem-F2-K0-K2 : _
lem-F2-K0-K2 = D002.lem-F2-K0-K2
lem-F2-K0-K3 : _
lem-F2-K0-K3 = D002.lem-F2-K0-K3
lem-F2-K1-K2 : _
lem-F2-K1-K2 = D002.lem-F2-K1-K2
lem-F2-K1-K3 : _
lem-F2-K1-K3 = D002.lem-F2-K1-K3
lem-F2-K2-K3 : _
lem-F2-K2-K3 = D002.lem-F2-K2-K3
lem-inv-SBOX⟨2·0·41·3⟩ : _
lem-inv-SBOX⟨2·0·41·3⟩ = D002.lem-inv-SBOX⟨2·0·41·3⟩
lem-invr-SBOX⟨2·0·41·3⟩ : _
lem-invr-SBOX⟨2·0·41·3⟩ = D002.lem-invr-SBOX⟨2·0·41·3⟩
lem-F1-order-Iat0 : _
lem-F1-order-Iat0 = D002.lem-F1-order-Iat0
lem-F1-order-Sat2 : _
lem-F1-order-Sat2 = D002.lem-F1-order-Sat2
lem-F1-order-Sat3 : _
lem-F1-order-Sat3 = D002.lem-F1-order-Sat3
lem-F1-order-Kat2 : _
lem-F1-order-Kat2 = D002.lem-F1-order-Kat2
lem-F1-order-Kat3 : _
lem-F1-order-Kat3 = D002.lem-F1-order-Kat3
lem-F1-order-SKat2 : _
lem-F1-order-SKat2 = D002.lem-F1-order-SKat2
lem-F1-order-SKat3 : _
lem-F1-order-SKat3 = D002.lem-F1-order-SKat3
lem-nf-order-CSat0 : _
lem-nf-order-CSat0 = D002.lem-nf-order-CSat0
lem-nf-order-CSat1 : _
lem-nf-order-CSat1 = D002.lem-nf-order-CSat1
lem-nf-order-CSat2 : _
lem-nf-order-CSat2 = D002.lem-nf-order-CSat2
lem-nat-SWbc-at02233440 : _
lem-nat-SWbc-at02233440 = D002.lem-nat-SWbc-at02233440
lem-nat-SWbc-at022440 : _
lem-nat-SWbc-at022440 = D002.lem-nat-SWbc-at022440
lem-sym-ab-at1441 : _
lem-sym-ab-at1441 = D002.lem-sym-ab-at1441
lem-nat-SWbc-at0210233441 : _
lem-nat-SWbc-at0210233441 = D002.lem-nat-SWbc-at0210233441
lem-nat-SWbc-at02102441 : _
lem-nat-SWbc-at02102441 = D002.lem-nat-SWbc-at02102441
lem-nat-SWbc-at233442 : _
lem-nat-SWbc-at233442 = D002.lem-nat-SWbc-at233442
lem-nat-SWbc-at2442 : _
lem-nat-SWbc-at2442 = D002.lem-nat-SWbc-at2442
lem-nat-SWbc-at143143 : _
lem-nat-SWbc-at143143 = D002.lem-nat-SWbc-at143143
lem-sym-ab-at0314213240 : _
lem-sym-ab-at0314213240 = D002.lem-sym-ab-at0314213240
lem-sym-ab-at03243240 : _
lem-sym-ab-at03243240 = D002.lem-sym-ab-at03243240
lem-nat-S-at01143043 : _
lem-nat-S-at01143043 = D002.lem-nat-S-at01143043
lem-nat-SWbc-at033440 : _
lem-nat-SWbc-at033440 = D002.lem-nat-SWbc-at033440
lem-nat-SWbc-at03243240 : _
lem-nat-SWbc-at03243240 = D002.lem-nat-SWbc-at03243240
lem-nat-SWbc-at03103441 : _
lem-nat-SWbc-at03103441 = D002.lem-nat-SWbc-at03103441
lem-nat-SWbc-at0310243241 : _
lem-nat-SWbc-at0310243241 = D002.lem-nat-SWbc-at0310243241
lem-cQ-at0310213442 : _
lem-cQ-at0310213442 = D002.lem-cQ-at0310213442
lem-sym-ab-at03122031 : _
lem-sym-ab-at03122031 = D002.lem-sym-ab-at03122031
lem-sym-ab-at0312243041 : _
lem-sym-ab-at0312243041 = D002.lem-sym-ab-at0312243041
lem-cQ-at0214233041 : _
lem-cQ-at0214233041 = D002.lem-cQ-at0214233041
lem-sym-ab-at0214233041 : _
lem-sym-ab-at0214233041 = D002.lem-sym-ab-at0214233041
lem-sym-ab-at03143041 : _
lem-sym-ab-at03143041 = D002.lem-sym-ab-at03143041
lem-sym-ab-at0213243041 : _
lem-sym-ab-at0213243041 = D002.lem-sym-ab-at0213243041
lem-sym-ab-at02142041 : _
lem-sym-ab-at02142041 = D002.lem-sym-ab-at02142041
lem-nat-SWbc-at02132130 : _
lem-nat-SWbc-at02132130 = D002.lem-nat-SWbc-at02132130
lem-nat-SWbc-at02132031 : _
lem-nat-SWbc-at02132031 = D002.lem-nat-SWbc-at02132031
lem-sym-ab-at02102441 : _
lem-sym-ab-at02102441 = D002.lem-sym-ab-at02102441
lem-cQ-at0213243041 : _
lem-cQ-at0213243041 = D002.lem-cQ-at0213243041
lem-sym-ab-at0314203241 : _
lem-sym-ab-at0314203241 = D002.lem-sym-ab-at0314203241
lem-nat-SWbc-at03122130 : _
lem-nat-SWbc-at03122130 = D002.lem-nat-SWbc-at03122130
lem-nat-SWbc-at03122031 : _
lem-nat-SWbc-at03122031 = D002.lem-nat-SWbc-at03122031
lem-sym-ab-at0310243241 : _
lem-sym-ab-at0310243241 = D002.lem-sym-ab-at0310243241
lem-sym-ab-at0330 : _
lem-sym-ab-at0330 = D002.lem-sym-ab-at0330
lem-sym-ab-at022330 : _
lem-sym-ab-at022330 = D002.lem-sym-ab-at022330
lem-sym-ab-at03122130 : _
lem-sym-ab-at03122130 = D002.lem-sym-ab-at03122130
sD004 : SD004
sD004 = lem-cQ-at021021 ∷ᵃ lem-cQ-at0210213443 ∷ᵃ lem-cQ-at03102132 ∷ᵃ lem-cQ-at032032 ∷ᵃ lem-cQ-at0410213243 ∷ᵃ lem-cQ-at04203243 ∷ᵃ lem-cQ-at13243142 ∷ᵃ lem-cQ-at13243241 ∷ᵃ lem-cQ-at14233142 ∷ᵃ lem-cQ-at14233241 ∷ᵃ lem-sym-ab ∷ᵃ lem-sym-ab-at03102132 ∷ᵃ lem-cQ-at0213243140 ∷ᵃ lem-cQ-at0220 ∷ᵃ nil
lem-cQ : _
lem-cQ = D004.lem-cQ sD004
lem-cQ-at0210243143 : _
lem-cQ-at0210243143 = D004.lem-cQ-at0210243143 sD004
lem-cQ-at243243 : _
lem-cQ-at243243 = D004.lem-cQ-at243243 sD004
lem-cQ-at122441 : _
lem-cQ-at122441 = D004.lem-cQ-at122441 sD004
lem-nat-SWbc : _
lem-nat-SWbc = D004.lem-nat-SWbc sD004
lem-box-tQ-at13243142 : _
lem-box-tQ-at13243142 = D004.lem-box-tQ-at13243142 sD004
lem-cQ-at1221 : _
lem-cQ-at1221 = D004.lem-cQ-at1221 sD004
lem-nat-SWbc-at1221 : _
lem-nat-SWbc-at1221 = D004.lem-nat-SWbc-at1221 sD004
lem-box-tQ-at13243241 : _
lem-box-tQ-at13243241 = D004.lem-box-tQ-at13243241 sD004
lem-cQ-at2332 : _
lem-cQ-at2332 = D004.lem-cQ-at2332 sD004
lem-cQ-at12243143 : _
lem-cQ-at12243143 = D004.lem-cQ-at12243143 sD004
lem-nat-SWbc-at13243142 : _
lem-nat-SWbc-at13243142 = D004.lem-nat-SWbc-at13243142 sD004
lem-cQ-at122331 : _
lem-cQ-at122331 = D004.lem-cQ-at122331 sD004
lem-nat-SWbc-at13243241 : _
lem-nat-SWbc-at13243241 = D004.lem-nat-SWbc-at13243241 sD004
lem-cQ-at132132 : _
lem-cQ-at132132 = D004.lem-cQ-at132132 sD004
lem-nat-SWbc-at12243143 : _
lem-nat-SWbc-at12243143 = D004.lem-nat-SWbc-at12243143 sD004
lem-box-tQ-at14233142 : _
lem-box-tQ-at14233142 = D004.lem-box-tQ-at14233142 sD004
lem-nat-SWbc-at14233142 : _
lem-nat-SWbc-at14233142 = D004.lem-nat-SWbc-at14233142 sD004
lem-tP-at14233142 : _
lem-tP-at14233142 = D004.lem-tP-at14233142 sD004
lem-cQ-at3443 : _
lem-cQ-at3443 = D004.lem-cQ-at3443 sD004
lem-cQ-at13213442 : _
lem-cQ-at13213442 = D004.lem-cQ-at13213442 sD004
lem-cQ-at1441 : _
lem-cQ-at1441 = D004.lem-cQ-at1441 sD004
lem-cQ-at1331 : _
lem-cQ-at1331 = D004.lem-cQ-at1331 sD004
lem-cQ-at2442 : _
lem-cQ-at2442 = D004.lem-cQ-at2442 sD004
lem-cQ-at12233441 : _
lem-cQ-at12233441 = D004.lem-cQ-at12233441 sD004
lem-cQ-at0110 : _
lem-cQ-at0110 = D004.lem-cQ-at0110 sD004
lem-cQ-at133441 : _
lem-cQ-at133441 = D004.lem-cQ-at133441 sD004
lem-nat-SWbc-at133441 : _
lem-nat-SWbc-at133441 = D004.lem-nat-SWbc-at133441 sD004
lem-tP-at13243241 : _
lem-tP-at13243241 = D004.lem-tP-at13243241 sD004
lem-cQ-at233442 : _
lem-cQ-at233442 = D004.lem-cQ-at233442 sD004
lem-tP-at021021 : _
lem-tP-at021021 = D004.lem-tP-at021021 sD004
lem-nat-SWbc-at13213442 : _
lem-nat-SWbc-at13213442 = D004.lem-nat-SWbc-at13213442 sD004
lem-tP-at13243142 : _
lem-tP-at13243142 = D004.lem-tP-at13243142 sD004
lem-tP-at03102132 : _
lem-tP-at03102132 = D004.lem-tP-at03102132 sD004
lem-tP-at0410213243 : _
lem-tP-at0410213243 = D004.lem-tP-at0410213243 sD004
lem-cQ-at043043 : _
lem-cQ-at043043 = D004.lem-cQ-at043043 sD004
lem-cQ-at0330 : _
lem-cQ-at0330 = D004.lem-cQ-at0330 sD004
lem-nat-SWbc-at043043 : _
lem-nat-SWbc-at043043 = D004.lem-nat-SWbc-at043043 sD004
lem-tP-at04203243 : _
lem-tP-at04203243 = D004.lem-tP-at04203243 sD004
lem-cQ-at0310243142 : _
lem-cQ-at0310243142 = D004.lem-cQ-at0310243142 sD004
lem-box-tQ-at0410213243 : _
lem-box-tQ-at0410213243 = D004.lem-box-tQ-at0410213243 sD004
lem-cQ-at0314203142 : _
lem-cQ-at0314203142 = D004.lem-cQ-at0314203142 sD004
lem-box-tQ-at04203243 : _
lem-box-tQ-at04203243 = D004.lem-box-tQ-at04203243 sD004
lem-nat-SWbc-at04203243 : _
lem-nat-SWbc-at04203243 = D004.lem-nat-SWbc-at04203243 sD004
lem-box-tQ-at032032 : _
lem-box-tQ-at032032 = D004.lem-box-tQ-at032032 sD004
lem-nat-SWbc-at032032 : _
lem-nat-SWbc-at032032 = D004.lem-nat-SWbc-at032032 sD004
lem-nat-SWbc-at0330 : _
lem-nat-SWbc-at0330 = D004.lem-nat-SWbc-at0330 sD004
lem-cQ-at0214203143 : _
lem-cQ-at0214203143 = D004.lem-cQ-at0214203143 sD004
lem-cQ-at0214213043 : _
lem-cQ-at0214213043 = D004.lem-cQ-at0214213043 sD004
lem-cQ-at0210233441 : _
lem-cQ-at0210233441 = D004.lem-cQ-at0210233441 sD004
lem-cQ-at14213243 : _
lem-cQ-at14213243 = D004.lem-cQ-at14213243 sD004
lem-cQ-at143143 : _
lem-cQ-at143143 = D004.lem-cQ-at143143 sD004
lem-nat-SWbc-at0210243143 : _
lem-nat-SWbc-at0210243143 = D004.lem-nat-SWbc-at0210243143 sD004
lem-tP-at0210213443 : _
lem-tP-at0210213443 = D004.lem-tP-at0210213443 sD004
lem-nat-SWbc-at243243 : _
lem-nat-SWbc-at243243 = D004.lem-nat-SWbc-at243243 sD004
lem-nat-SWbc-at1441 : _
lem-nat-SWbc-at1441 = D004.lem-nat-SWbc-at1441 sD004
lem-box-tQ-at14233241 : _
lem-box-tQ-at14233241 = D004.lem-box-tQ-at14233241 sD004
lem-tP-at14233241 : _
lem-tP-at14233241 = D004.lem-tP-at14233241 sD004
lem-cQ-at12213443 : _
lem-cQ-at12213443 = D004.lem-cQ-at12213443 sD004
lem-cQ-at0314213042 : _
lem-cQ-at0314213042 = D004.lem-cQ-at0314213042 sD004
lem-cQ-at0213203441 : _
lem-cQ-at0213203441 = D004.lem-cQ-at0213203441 sD004
lem-tP-at032032 : _
lem-tP-at032032 = D004.lem-tP-at032032 sD004
lem-cQ-at0312243140 : _
lem-cQ-at0312243140 = D004.lem-cQ-at0312243140 sD004
lem-nat-SWbc-at0312243140 : _
lem-nat-SWbc-at0312243140 = D004.lem-nat-SWbc-at0312243140 sD004
lem-cQ-at033440 : _
lem-cQ-at033440 = D004.lem-cQ-at033440 sD004
lem-cQ-at0312213440 : _
lem-cQ-at0312213440 = D004.lem-cQ-at0312213440 sD004
lem-nat-SWbc-at0312213440 : _
lem-nat-SWbc-at0312213440 = D004.lem-nat-SWbc-at0312213440 sD004
lem-cQ-at022330 : _
lem-cQ-at022330 = D004.lem-cQ-at022330 sD004
lem-box-tQ-at0220 : _
lem-box-tQ-at0220 = D004.lem-box-tQ-at0220 sD004
lem-tP-at0220 : _
lem-tP-at0220 = D004.lem-tP-at0220 sD004
lem-box-tQ-at0213243140 : _
lem-box-tQ-at0213243140 = D004.lem-box-tQ-at0213243140 sD004
lem-nat-SWbc-at0213243140 : _
lem-nat-SWbc-at0213243140 = D004.lem-nat-SWbc-at0213243140 sD004
lem-cQ-at02233440 : _
lem-cQ-at02233440 = D004.lem-cQ-at02233440 sD004
lem-cQ-at0213213440 : _
lem-cQ-at0213213440 = D004.lem-cQ-at0213213440 sD004
lem-nat-SWbc-at0213213440 : _
lem-nat-SWbc-at0213213440 = D004.lem-nat-SWbc-at0213213440 sD004
lem-tP-at0213243140 : _
lem-tP-at0213243140 = D004.lem-tP-at0213243140 sD004
lem-nat-SWbc-at122331 : _
lem-nat-SWbc-at122331 = D004.lem-nat-SWbc-at122331 sD004
lem-nat-SWbc-at2332 : _
lem-nat-SWbc-at2332 = D004.lem-nat-SWbc-at2332 sD004
lem-box-tQ-at0210213443 : _
lem-box-tQ-at0210213443 = D004.lem-box-tQ-at0210213443 sD004
lem-box-perm-2134-at03102132 : _
lem-box-perm-2134-at03102132 = D004.lem-box-perm-2134-at03102132 sD004
lem-box-tQ-at03102132 : _
lem-box-tQ-at03102132 = D004.lem-box-tQ-at03102132 sD004
lem-nat-SWbc-at03102132 : _
lem-nat-SWbc-at03102132 = D004.lem-nat-SWbc-at03102132 sD004
lem-cQ-at022440 : _
lem-cQ-at022440 = D004.lem-cQ-at022440 sD004
lem-cQ-at02102441 : _
lem-cQ-at02102441 = D004.lem-cQ-at02102441 sD004
lem-sym-ab-at0310213442 : _
lem-sym-ab-at0310213442 = D003.lem-sym-ab-at0310213442
lem-cQ-at03203442 : _
lem-cQ-at03203442 = D003.lem-cQ-at03203442
lem-sym-ab-at03203442 : _
lem-sym-ab-at03203442 = D003.lem-sym-ab-at03203442
lem-sym-ab-at02132130 : _
lem-sym-ab-at02132130 = D003.lem-sym-ab-at02132130
lem-sym-ab-at031031 : _
lem-sym-ab-at031031 = D003.lem-sym-ab-at031031
lem-sym-ab-at03243042 : _
lem-sym-ab-at03243042 = D003.lem-sym-ab-at03243042
lem-sym-ab-at0314213042 : _
lem-sym-ab-at0314213042 = D003.lem-sym-ab-at0314213042
lem-sym-ab-at142142 : _
lem-sym-ab-at142142 = D003.lem-sym-ab-at142142
lem-sym-ab-at2442 : _
lem-sym-ab-at2442 = D003.lem-sym-ab-at2442
lem-sym-ab-at02102331 : _
lem-sym-ab-at02102331 = D003.lem-sym-ab-at02102331
lem-sym-ab-at02132031 : _
lem-sym-ab-at02132031 = D003.lem-sym-ab-at02132031
lem-F4-I-K2-at02132031 : _
lem-F4-I-K2-at02132031 = D003.lem-F4-I-K2-at02132031
lem-F4-S3-K2-at02132031 : _
lem-F4-S3-K2-at02132031 = D003.lem-F4-S3-K2-at02132031
lem-F4-K2-K2-at02132031 : _
lem-F4-K2-K2-at02132031 = D003.lem-F4-K2-K2-at02132031
lem-F4-I-S3-at02132031 : _
lem-F4-I-S3-at02132031 = D003.lem-F4-I-S3-at02132031
lem-F4-S3-S3-at02132031 : _
lem-F4-S3-S3-at02132031 = D003.lem-F4-S3-S3-at02132031
lem-F4-S3-I-at02132031 : _
lem-F4-S3-I-at02132031 = D003.lem-F4-S3-I-at02132031
lem-nat-SWbc-at041041 : _
lem-nat-SWbc-at041041 = D003.lem-nat-SWbc-at041041
lem-nat-SWbc-at04233240 : _
lem-nat-SWbc-at04233240 = D003.lem-nat-SWbc-at04233240
lem-nat-SWbc-at0413203142 : _
lem-nat-SWbc-at0413203142 = D003.lem-nat-SWbc-at0413203142
lem-nat-SWbc-at0413213042 : _
lem-nat-SWbc-at0413213042 = D003.lem-nat-SWbc-at0413213042
lem-nat-SWbc-at0440 : _
lem-nat-SWbc-at0440 = D003.lem-nat-SWbc-at0440
sD005 : SD005
sD005 = lem-cQ-at021021 ∷ᵃ lem-sym-ab-at0210243143 ∷ᵃ lem-sym-ab-at032032 ∷ᵃ lem-sym-ab-at1221 ∷ᵃ lem-cQ-at0213243041 ∷ᵃ lem-cQ-at0214233041 ∷ᵃ lem-cQ-at0310213442 ∷ᵃ lem-sym-ab-at021021 ∷ᵃ lem-sym-ab-at0220 ∷ᵃ lem-cQ-at03203442 ∷ᵃ nil
lem-nat-SWbc-at12213443 : _
lem-nat-SWbc-at12213443 = D005.lem-nat-SWbc-at12213443 sD005
lem-nat-SWbc-at14233241 : _
lem-nat-SWbc-at14233241 = D005.lem-nat-SWbc-at14233241 sD005
lem-cQ-at03143140 : _
lem-cQ-at03143140 = D005.lem-cQ-at03143140 sD005
lem-nat-SWbc-at03143140 : _
lem-nat-SWbc-at03143140 = D005.lem-nat-SWbc-at03143140 sD005
lem-cQ-at0314213240 : _
lem-cQ-at0314213240 = D005.lem-cQ-at0314213240 sD005
lem-cQ-at03243240 : _
lem-cQ-at03243240 = D005.lem-cQ-at03243240 sD005
lem-nat-SWbc-at0314213240 : _
lem-nat-SWbc-at0314213240 = D005.lem-nat-SWbc-at0314213240 sD005
lem-cQ-at03103441 : _
lem-cQ-at03103441 = D005.lem-cQ-at03103441 sD005
lem-cQ-at0310243241 : _
lem-cQ-at0310243241 = D005.lem-cQ-at0310243241 sD005
lem-nat-SWbc-at0310243142 : _
lem-nat-SWbc-at0310243142 = D005.lem-nat-SWbc-at0310243142 sD005
lem-box-tQ-at0310213442 : _
lem-box-tQ-at0310213442 = D005.lem-box-tQ-at0310213442 sD005
lem-nat-SWbc-at0310213442 : _
lem-nat-SWbc-at0310213442 = D005.lem-nat-SWbc-at0310213442 sD005
lem-cQ-at0312203441 : _
lem-cQ-at0312203441 = D005.lem-cQ-at0312203441 sD005
lem-nat-SWbc-at0312203441 : _
lem-nat-SWbc-at0312203441 = D005.lem-nat-SWbc-at0312203441 sD005
lem-cQ-at0312243041 : _
lem-cQ-at0312243041 = D005.lem-cQ-at0312243041 sD005
lem-nat-SWbc-at0312243041 : _
lem-nat-SWbc-at0312243041 = D005.lem-nat-SWbc-at0312243041 sD005
lem-nat-SWbc-at3443 : _
lem-nat-SWbc-at3443 = D005.lem-nat-SWbc-at3443 sD005
lem-cQ-at03122031 : _
lem-cQ-at03122031 = D005.lem-cQ-at03122031 sD005
lem-cQ-at031031 : _
lem-cQ-at031031 = D005.lem-cQ-at031031 sD005
lem-nat-SWbc-at031031 : _
lem-nat-SWbc-at031031 = D005.lem-nat-SWbc-at031031 sD005
lem-cQ-at03143041 : _
lem-cQ-at03143041 = D005.lem-cQ-at03143041 sD005
lem-nat-SWbc-at03143041 : _
lem-nat-SWbc-at03143041 = D005.lem-nat-SWbc-at03143041 sD005
lem-cQ-at0314203241 : _
lem-cQ-at0314203241 = D005.lem-cQ-at0314203241 sD005
lem-cQ-at02142041 : _
lem-cQ-at02142041 = D005.lem-cQ-at02142041 sD005
lem-tP-at0214233041 : _
lem-tP-at0214233041 = D005.lem-tP-at0214233041 sD005
lem-nat-SWbc-at0314203241 : _
lem-nat-SWbc-at0314203241 = D005.lem-nat-SWbc-at0314203241 sD005
lem-box-tQ-at0214233041 : _
lem-box-tQ-at0214233041 = D005.lem-box-tQ-at0214233041 sD005
lem-nat-SWbc-at0210213443 : _
lem-nat-SWbc-at0210213443 = D005.lem-nat-SWbc-at0210213443 sD005
lem-cQ-at02132130 : _
lem-cQ-at02132130 = D005.lem-cQ-at02132130 sD005
lem-cQ-at02132031 : _
lem-cQ-at02132031 = D005.lem-cQ-at02132031 sD005
lem-tP-at0310213442 : _
lem-tP-at0310213442 = D005.lem-tP-at0310213442 sD005
lem-tP-at0213243041 : _
lem-tP-at0213243041 = D005.lem-tP-at0213243041 sD005
lem-box-tQ-at0213243041 : _
lem-box-tQ-at0213243041 = D005.lem-box-tQ-at0213243041 sD005
lem-box-tQ-at021021 : _
lem-box-tQ-at021021 = D005.lem-box-tQ-at021021 sD005
lem-cQ-at03122130 : _
lem-cQ-at03122130 = D005.lem-cQ-at03122130 sD005
lem-box-tQ-at03203442 : _
lem-box-tQ-at03203442 = D005.lem-box-tQ-at03203442 sD005
lem-nat-SWbc-at021021 : _
lem-nat-SWbc-at021021 = D005.lem-nat-SWbc-at021021 sD005
lem-cQ-at02102331 : _
lem-cQ-at02102331 = D005.lem-cQ-at02102331 sD005
lem-cQ-at03243042 : _
lem-cQ-at03243042 = D005.lem-cQ-at03243042 sD005
lem-cQ-at142142 : _
lem-cQ-at142142 = D005.lem-cQ-at142142 sD005
lem-nat-SWbc-at142142 : _
lem-nat-SWbc-at142142 = D005.lem-nat-SWbc-at142142 sD005
lem-nat-SWbc-at02102331 : _
lem-nat-SWbc-at02102331 = D005.lem-nat-SWbc-at02102331 sD005
lem-box-perm-2134-at0210243143 : _
lem-box-perm-2134-at0210243143 = D005.lem-box-perm-2134-at0210243143 sD005
lem-cQ-at04122041 : _
lem-cQ-at04122041 = D005.lem-cQ-at04122041 sD005
lem-nat-SWbc-at04122041 : _
lem-nat-SWbc-at04122041 = D005.lem-nat-SWbc-at04122041 sD005
lem-cQ-at0412233041 : _
lem-cQ-at0412233041 = D005.lem-cQ-at0412233041 sD005
lem-nat-SWbc-at0410213243 : _
lem-nat-SWbc-at0410213243 = D005.lem-nat-SWbc-at0410213243 sD005
lem-cQ-at04103143 : _
lem-cQ-at04103143 = D005.lem-cQ-at04103143 sD005
lem-cQ-at04233042 : _
lem-cQ-at04233042 = D005.lem-cQ-at04233042 sD005
lem-nat-SWbc-at0412233041 : _
lem-nat-SWbc-at0412233041 = D005.lem-nat-SWbc-at0412233041 sD005
lem-cQ-at041041 : _
lem-cQ-at041041 = D005.lem-cQ-at041041 sD005
lem-cQ-at0410233241 : _
lem-cQ-at0410233241 = D005.lem-cQ-at0410233241 sD005
lem-cQ-at0412213043 : _
lem-cQ-at0412213043 = D005.lem-cQ-at0412213043 sD005
lem-cQ-at0413213240 : _
lem-cQ-at0413213240 = D005.lem-cQ-at0413213240 sD005
lem-cQ-at04233240 : _
lem-cQ-at04233240 = D005.lem-cQ-at04233240 sD005
lem-cQ-at0440 : _
lem-cQ-at0440 = D005.lem-cQ-at0440 sD005
lem-cQ-at0413203142 : _
lem-cQ-at0413203142 = D005.lem-cQ-at0413203142 sD005
lem-cQ-at02142140 : _
lem-cQ-at02142140 = D005.lem-cQ-at02142140 sD005
lem-cQ-at0413213042 : _
lem-cQ-at0413213042 = D005.lem-cQ-at0413213042 sD005
lem-cQ-at0412233140 : _
lem-cQ-at0412233140 = D005.lem-cQ-at0412233140 sD005
lem-nat-SWbc-at0412233140 : _
lem-nat-SWbc-at0412233140 = D005.lem-nat-SWbc-at0412233140 sD005
lem-cQ-at0410233142 : _
lem-cQ-at0410233142 = D005.lem-cQ-at0410233142 sD005
lem-cQ-at04122140 : _
lem-cQ-at04122140 = D005.lem-cQ-at04122140 sD005
lem-nat-SWbc-at04122140 : _
lem-nat-SWbc-at04122140 = D005.lem-nat-SWbc-at04122140 sD005
lem-cQ-at0413203241 : _
lem-cQ-at0413203241 = D005.lem-cQ-at0413203241 sD005
lem-cQ-at04133140 : _
lem-cQ-at04133140 = D005.lem-cQ-at04133140 sD005
lem-nat-SWbc-at04133140 : _
lem-nat-SWbc-at04133140 = D005.lem-nat-SWbc-at04133140 sD005
lem-nat-SWbc-at0413213240 : _
lem-nat-SWbc-at0413213240 = D005.lem-nat-SWbc-at0413213240 sD005
sD007 : SD007
sD007 = lem-box-perm-2134-at03102132 ∷ᵃ lem-box-tQ-at0210213443 ∷ᵃ lem-box-tQ-at0213243140 ∷ᵃ lem-box-tQ-at0220 ∷ᵃ lem-box-tQ-at03102132 ∷ᵃ lem-box-tQ-at0410213243 ∷ᵃ lem-box-tQ-at14233241 ∷ᵃ lem-cQ-at02102441 ∷ᵃ lem-cQ-at0213213440 ∷ᵃ lem-cQ-at0214203143 ∷ᵃ lem-cQ-at022330 ∷ᵃ lem-cQ-at02233440 ∷ᵃ lem-cQ-at022440 ∷ᵃ lem-cQ-at033440 ∷ᵃ lem-cQ-at12243143 ∷ᵃ lem-cQ-at14213243 ∷ᵃ lem-cQ-at1441 ∷ᵃ lem-cQ-at2442 ∷ᵃ lem-tP-at021021 ∷ᵃ lem-tP-at0210213443 ∷ᵃ lem-tP-at0213243140 ∷ᵃ lem-tP-at03102132 ∷ᵃ lem-tP-at032032 ∷ᵃ lem-box-perm-2134-at0210243143 ∷ᵃ lem-box-tQ-at021021 ∷ᵃ lem-box-tQ-at0213243041 ∷ᵃ lem-box-tQ-at0214233041 ∷ᵃ lem-box-tQ-at0310213442 ∷ᵃ lem-cQ-at02102331 ∷ᵃ lem-cQ-at02132031 ∷ᵃ lem-cQ-at02132130 ∷ᵃ lem-cQ-at02142041 ∷ᵃ lem-cQ-at0310243241 ∷ᵃ lem-cQ-at031031 ∷ᵃ lem-cQ-at03103441 ∷ᵃ lem-cQ-at03122031 ∷ᵃ lem-cQ-at0312203441 ∷ᵃ lem-cQ-at03122130 ∷ᵃ lem-cQ-at0312243041 ∷ᵃ lem-cQ-at0314203241 ∷ᵃ lem-cQ-at0314213240 ∷ᵃ lem-cQ-at03143041 ∷ᵃ lem-cQ-at03143140 ∷ᵃ lem-cQ-at03243042 ∷ᵃ lem-cQ-at03243240 ∷ᵃ lem-cQ-at04103143 ∷ᵃ lem-cQ-at04122041 ∷ᵃ lem-cQ-at0412233041 ∷ᵃ lem-cQ-at04233042 ∷ᵃ lem-cQ-at142142 ∷ᵃ lem-tP-at0213243041 ∷ᵃ lem-tP-at0214233041 ∷ᵃ lem-tP-at0310213442 ∷ᵃ nil
lem-box-tQ-at02233440 : _
lem-box-tQ-at02233440 = D007.lem-box-tQ-at02233440 sD007
lem-box-tQ-at0213213440 : _
lem-box-tQ-at0213213440 = D007.lem-box-tQ-at0213213440 sD007
lem-P-box-at0213243140 : _
lem-P-box-at0213243140 = D007.lem-P-box-at0213243140 sD007
lem-VPQ-at0213243140 : _
lem-VPQ-at0213243140 = D007.lem-VPQ-at0213243140 sD007
lem-CXbc-box-at0220 : _
lem-CXbc-box-at0220 = D007.lem-CXbc-box-at0220 sD007
lem-CXcb-box-at0220 : _
lem-CXcb-box-at0220 = D007.lem-CXcb-box-at0220 sD007
lem-nat-SWbc-at0220 : _
lem-nat-SWbc-at0220 = D007.lem-nat-SWbc-at0220 sD007
lem-tP-at022330 : _
lem-tP-at022330 = D007.lem-tP-at022330 sD007
lem-tP-at14213243 : _
lem-tP-at14213243 = D007.lem-tP-at14213243 sD007
lem-CXbc-box-at03102132 : _
lem-CXbc-box-at03102132 = D007.lem-CXbc-box-at03102132 sD007
lem-CXcb-box-at03102132 : _
lem-CXcb-box-at03102132 = D007.lem-CXcb-box-at03102132 sD007
lem-tP-at0214203143 : _
lem-tP-at0214203143 = D007.lem-tP-at0214203143 sD007
lem-tP-at022440 : _
lem-tP-at022440 = D007.lem-tP-at022440 sD007
lem-box-tQ-at022440 : _
lem-box-tQ-at022440 = D007.lem-box-tQ-at022440 sD007
lem-tP-at02233440 : _
lem-tP-at02233440 = D007.lem-tP-at02233440 sD007
lem-tP-at1441 : _
lem-tP-at1441 = D007.lem-tP-at1441 sD007
lem-tP-at02102441 : _
lem-tP-at02102441 = D007.lem-tP-at02102441 sD007
lem-box-tQ-at02102441 : _
lem-box-tQ-at02102441 = D007.lem-box-tQ-at02102441 sD007
lem-tP-at2442 : _
lem-tP-at2442 = D007.lem-tP-at2442 sD007
lem-tP-at12243143 : _
lem-tP-at12243143 = D007.lem-tP-at12243143 sD007
lem-CXbc-box-at14233241 : _
lem-CXbc-box-at14233241 = D007.lem-CXbc-box-at14233241 sD007
lem-CXcb-box-at14233241 : _
lem-CXcb-box-at14233241 = D007.lem-CXcb-box-at14233241 sD007
lem-box-tQ-at03143140 : _
lem-box-tQ-at03143140 = D007.lem-box-tQ-at03143140 sD007
lem-tP-at0314213240 : _
lem-tP-at0314213240 = D007.lem-tP-at0314213240 sD007
lem-box-tQ-at03243240 : _
lem-box-tQ-at03243240 = D007.lem-box-tQ-at03243240 sD007
lem-box-tQ-at0314213240 : _
lem-box-tQ-at0314213240 = D007.lem-box-tQ-at0314213240 sD007
lem-tP-at03143140 : _
lem-tP-at03143140 = D007.lem-tP-at03143140 sD007
lem-tP-at03243240 : _
lem-tP-at03243240 = D007.lem-tP-at03243240 sD007
lem-tP-at033440 : _
lem-tP-at033440 = D007.lem-tP-at033440 sD007
lem-box-tQ-at03103441 : _
lem-box-tQ-at03103441 = D007.lem-box-tQ-at03103441 sD007
lem-tP-at0310243241 : _
lem-tP-at0310243241 = D007.lem-tP-at0310243241 sD007
lem-box-tQ-at0310243241 : _
lem-box-tQ-at0310243241 = D007.lem-box-tQ-at0310243241 sD007
lem-tP-at03103441 : _
lem-tP-at03103441 = D007.lem-tP-at03103441 sD007
lem-CXbc-box-at0310213442 : _
lem-CXbc-box-at0310213442 = D007.lem-CXbc-box-at0310213442 sD007
lem-CXcb-box-at0310213442 : _
lem-CXcb-box-at0310213442 = D007.lem-CXcb-box-at0310213442 sD007
lem-box-tQ-at0312203441 : _
lem-box-tQ-at0312203441 = D007.lem-box-tQ-at0312203441 sD007
lem-tP-at0312243041 : _
lem-tP-at0312243041 = D007.lem-tP-at0312243041 sD007
lem-box-tQ-at0312243041 : _
lem-box-tQ-at0312243041 = D007.lem-box-tQ-at0312243041 sD007
lem-tP-at0312203441 : _
lem-tP-at0312203441 = D007.lem-tP-at0312203441 sD007
lem-box-tQ-at03122031 : _
lem-box-tQ-at03122031 = D007.lem-box-tQ-at03122031 sD007
lem-box-tQ-at031031 : _
lem-box-tQ-at031031 = D007.lem-box-tQ-at031031 sD007
lem-tP-at031031 : _
lem-tP-at031031 = D007.lem-tP-at031031 sD007
lem-P-box-at03102132 : _
lem-P-box-at03102132 = D007.lem-P-box-at03102132 sD007
lem-box-tQ-at03143041 : _
lem-box-tQ-at03143041 = D007.lem-box-tQ-at03143041 sD007
lem-box-tQ-at0314203241 : _
lem-box-tQ-at0314203241 = D007.lem-box-tQ-at0314203241 sD007
lem-box-tQ-at02142041 : _
lem-box-tQ-at02142041 = D007.lem-box-tQ-at02142041 sD007
lem-nat-SWbc-at02142041 : _
lem-nat-SWbc-at02142041 = D007.lem-nat-SWbc-at02142041 sD007
lem-VPQ-at0214233041 : _
lem-VPQ-at0214233041 = D007.lem-VPQ-at0214233041 sD007
lem-P-box-at0214233041 : _
lem-P-box-at0214233041 = D007.lem-P-box-at0214233041 sD007
lem-CXbc-box-at0210213443 : _
lem-CXbc-box-at0210213443 = D007.lem-CXbc-box-at0210213443 sD007
lem-CXcb-box-at0210213443 : _
lem-CXcb-box-at0210213443 = D007.lem-CXcb-box-at0210213443 sD007
lem-P-box-at0210213443 : _
lem-P-box-at0210213443 = D007.lem-P-box-at0210213443 sD007
lem-CXbc-box-at0214233041 : _
lem-CXbc-box-at0214233041 = D007.lem-CXbc-box-at0214233041 sD007
lem-CXcb-box-at0214233041 : _
lem-CXcb-box-at0214233041 = D007.lem-CXcb-box-at0214233041 sD007
lem-nat-SWbc-at0214233041 : _
lem-nat-SWbc-at0214233041 = D007.lem-nat-SWbc-at0214233041 sD007
lem-box-tQ-at02132130 : _
lem-box-tQ-at02132130 = D007.lem-box-tQ-at02132130 sD007
lem-tP-at03143041 : _
lem-tP-at03143041 = D007.lem-tP-at03143041 sD007
lem-tP-at02132031 : _
lem-tP-at02132031 = D007.lem-tP-at02132031 sD007
lem-P-box-at0310213442 : _
lem-P-box-at0310213442 = D007.lem-P-box-at0310213442 sD007
lem-VPQ-at0310213442 : _
lem-VPQ-at0310213442 = D007.lem-VPQ-at0310213442 sD007
lem-box-tQ-at02132031 : _
lem-box-tQ-at02132031 = D007.lem-box-tQ-at02132031 sD007
lem-tP-at02132130 : _
lem-tP-at02132130 = D007.lem-tP-at02132130 sD007
lem-VPQ-at0213243041 : _
lem-VPQ-at0213243041 = D007.lem-VPQ-at0213243041 sD007
lem-P-box-at0213243041 : _
lem-P-box-at0213243041 = D007.lem-P-box-at0213243041 sD007
lem-box-tQ-at03122130 : _
lem-box-tQ-at03122130 = D007.lem-box-tQ-at03122130 sD007
lem-P-box-at021021 : _
lem-P-box-at021021 = D007.lem-P-box-at021021 sD007
lem-tP-at03122031 : _
lem-tP-at03122031 = D007.lem-tP-at03122031 sD007
lem-tP-at03122130 : _
lem-tP-at03122130 = D007.lem-tP-at03122130 sD007
lem-t-cP-at03102132 : _
lem-t-cP-at03102132 = D007.lem-t-cP-at03102132 sD007
lem-tP-at02142041 : _
lem-tP-at02142041 = D007.lem-tP-at02142041 sD007
lem-tP-at0314203241 : _
lem-tP-at0314203241 = D007.lem-tP-at0314203241 sD007
lem-CXbc-box-at021021 : _
lem-CXbc-box-at021021 = D007.lem-CXbc-box-at021021 sD007
lem-CXcb-box-at021021 : _
lem-CXcb-box-at021021 = D007.lem-CXcb-box-at021021 sD007
lem-tP-at02102331 : _
lem-tP-at02102331 = D007.lem-tP-at02102331 sD007
lem-box-tQ-at03243042 : _
lem-box-tQ-at03243042 = D007.lem-box-tQ-at03243042 sD007
lem-box-tQ-at142142 : _
lem-box-tQ-at142142 = D007.lem-box-tQ-at142142 sD007
lem-tP-at03243042 : _
lem-tP-at03243042 = D007.lem-tP-at03243042 sD007
lem-box-tQ-at02102331 : _
lem-box-tQ-at02102331 = D007.lem-box-tQ-at02102331 sD007
lem-tP-at142142 : _
lem-tP-at142142 = D007.lem-tP-at142142 sD007
lem-t-cP-at032032 : _
lem-t-cP-at032032 = D007.lem-t-cP-at032032 sD007
lem-box-tQ-at04122041 : _
lem-box-tQ-at04122041 = D007.lem-box-tQ-at04122041 sD007
lem-tP-at0412233041 : _
lem-tP-at0412233041 = D007.lem-tP-at0412233041 sD007
lem-tP-at04122041 : _
lem-tP-at04122041 = D007.lem-tP-at04122041 sD007
lem-CXbc-box-at0410213243 : _
lem-CXbc-box-at0410213243 = D007.lem-CXbc-box-at0410213243 sD007
lem-CXcb-box-at0410213243 : _
lem-CXcb-box-at0410213243 = D007.lem-CXcb-box-at0410213243 sD007
lem-box-tQ-at04103143 : _
lem-box-tQ-at04103143 = D007.lem-box-tQ-at04103143 sD007
lem-tP-at04103143 : _
lem-tP-at04103143 = D007.lem-tP-at04103143 sD007
lem-box-tQ-at04233042 : _
lem-box-tQ-at04233042 = D007.lem-box-tQ-at04233042 sD007
lem-tP-at04233042 : _
lem-tP-at04233042 = D007.lem-tP-at04233042 sD007
sD006 : SD006
sD006 = lem-box-tQ-at0213243140 ∷ᵃ lem-box-tQ-at0220 ∷ᵃ lem-box-tQ-at032032 ∷ᵃ lem-box-tQ-at04203243 ∷ᵃ lem-box-tQ-at13243142 ∷ᵃ lem-box-tQ-at13243241 ∷ᵃ lem-box-tQ-at14233142 ∷ᵃ lem-box-tQ-at14233241 ∷ᵃ lem-cQ ∷ᵃ lem-cQ-at0110 ∷ᵃ lem-cQ-at0210233441 ∷ᵃ lem-cQ-at0210243143 ∷ᵃ lem-cQ-at0213203441 ∷ᵃ lem-cQ-at0214203143 ∷ᵃ lem-cQ-at0214213043 ∷ᵃ lem-cQ-at022330 ∷ᵃ lem-cQ-at0310243142 ∷ᵃ lem-cQ-at0312213440 ∷ᵃ lem-cQ-at0312243140 ∷ᵃ lem-cQ-at0314203142 ∷ᵃ lem-cQ-at0314213042 ∷ᵃ lem-cQ-at0330 ∷ᵃ lem-cQ-at033440 ∷ᵃ lem-cQ-at043043 ∷ᵃ lem-cQ-at1221 ∷ᵃ lem-cQ-at12213443 ∷ᵃ lem-cQ-at122331 ∷ᵃ lem-cQ-at12233441 ∷ᵃ lem-cQ-at12243143 ∷ᵃ lem-cQ-at122441 ∷ᵃ lem-cQ-at132132 ∷ᵃ lem-cQ-at13213442 ∷ᵃ lem-cQ-at1331 ∷ᵃ lem-cQ-at133441 ∷ᵃ lem-cQ-at14213243 ∷ᵃ lem-cQ-at143143 ∷ᵃ lem-cQ-at1441 ∷ᵃ lem-cQ-at2332 ∷ᵃ lem-cQ-at233442 ∷ᵃ lem-cQ-at243243 ∷ᵃ lem-cQ-at2442 ∷ᵃ lem-cQ-at3443 ∷ᵃ lem-tP-at021021 ∷ᵃ lem-tP-at0210213443 ∷ᵃ lem-tP-at0220 ∷ᵃ lem-tP-at03102132 ∷ᵃ lem-tP-at032032 ∷ᵃ lem-tP-at0410213243 ∷ᵃ lem-tP-at04203243 ∷ᵃ lem-tP-at13243142 ∷ᵃ lem-tP-at13243241 ∷ᵃ lem-tP-at14233142 ∷ᵃ lem-tP-at14233241 ∷ᵃ nil
lem-tP : _
lem-tP = D006.lem-tP sD006
lem-box-tQ : _
lem-box-tQ = D006.lem-box-tQ sD006
lem-tP-at0210243143 : _
lem-tP-at0210243143 = D006.lem-tP-at0210243143 sD006
lem-box-tQ-at0210243143 : _
lem-box-tQ-at0210243143 = D006.lem-box-tQ-at0210243143 sD006
lem-tP-at243243 : _
lem-tP-at243243 = D006.lem-tP-at243243 sD006
lem-box-tQ-at243243 : _
lem-box-tQ-at243243 = D006.lem-box-tQ-at243243 sD006
lem-tP-at122441 : _
lem-tP-at122441 = D006.lem-tP-at122441 sD006
lem-box-tQ-at122441 : _
lem-box-tQ-at122441 = D006.lem-box-tQ-at122441 sD006
lem-box-tQ-at1221 : _
lem-box-tQ-at1221 = D006.lem-box-tQ-at1221 sD006
lem-tP-at1221 : _
lem-tP-at1221 = D006.lem-tP-at1221 sD006
lem-box-tQ-at2332 : _
lem-box-tQ-at2332 = D006.lem-box-tQ-at2332 sD006
lem-tP-at2332 : _
lem-tP-at2332 = D006.lem-tP-at2332 sD006
lem-box-tQ-at12243143 : _
lem-box-tQ-at12243143 = D006.lem-box-tQ-at12243143 sD006
lem-CXbc-box-at13243142 : _
lem-CXbc-box-at13243142 = D006.lem-CXbc-box-at13243142 sD006
lem-CXcb-box-at13243142 : _
lem-CXcb-box-at13243142 = D006.lem-CXcb-box-at13243142 sD006
lem-box-tQ-at122331 : _
lem-box-tQ-at122331 = D006.lem-box-tQ-at122331 sD006
lem-tP-at122331 : _
lem-tP-at122331 = D006.lem-tP-at122331 sD006
lem-CXbc-box-at13243241 : _
lem-CXbc-box-at13243241 = D006.lem-CXbc-box-at13243241 sD006
lem-CXcb-box-at13243241 : _
lem-CXcb-box-at13243241 = D006.lem-CXcb-box-at13243241 sD006
lem-box-tQ-at132132 : _
lem-box-tQ-at132132 = D006.lem-box-tQ-at132132 sD006
lem-tP-at132132 : _
lem-tP-at132132 = D006.lem-tP-at132132 sD006
lem-CXbc-box-at14233142 : _
lem-CXbc-box-at14233142 = D006.lem-CXbc-box-at14233142 sD006
lem-CXcb-box-at14233142 : _
lem-CXcb-box-at14233142 = D006.lem-CXcb-box-at14233142 sD006
lem-P-box-at14233142 : _
lem-P-box-at14233142 = D006.lem-P-box-at14233142 sD006
lem-VPQ-at14233142 : _
lem-VPQ-at14233142 = D006.lem-VPQ-at14233142 sD006
lem-box-tQ-at3443 : _
lem-box-tQ-at3443 = D006.lem-box-tQ-at3443 sD006
lem-box-tQ-at13213442 : _
lem-box-tQ-at13213442 = D006.lem-box-tQ-at13213442 sD006
lem-tP-at13213442 : _
lem-tP-at13213442 = D006.lem-tP-at13213442 sD006
lem-box-tQ-at1441 : _
lem-box-tQ-at1441 = D006.lem-box-tQ-at1441 sD006
lem-box-tQ-at1331 : _
lem-box-tQ-at1331 = D006.lem-box-tQ-at1331 sD006
lem-tP-at1331 : _
lem-tP-at1331 = D006.lem-tP-at1331 sD006
lem-box-tQ-at2442 : _
lem-box-tQ-at2442 = D006.lem-box-tQ-at2442 sD006
lem-box-tQ-at12233441 : _
lem-box-tQ-at12233441 = D006.lem-box-tQ-at12233441 sD006
lem-tP-at0110 : _
lem-tP-at0110 = D006.lem-tP-at0110 sD006
lem-box-tQ-at133441 : _
lem-box-tQ-at133441 = D006.lem-box-tQ-at133441 sD006
lem-P-box-at13243241 : _
lem-P-box-at13243241 = D006.lem-P-box-at13243241 sD006
lem-VPQ-at13243241 : _
lem-VPQ-at13243241 = D006.lem-VPQ-at13243241 sD006
lem-box-tQ-at233442 : _
lem-box-tQ-at233442 = D006.lem-box-tQ-at233442 sD006
lem-VPQ-at021021 : _
lem-VPQ-at021021 = D006.lem-VPQ-at021021 sD006
lem-P-box-at13243142 : _
lem-P-box-at13243142 = D006.lem-P-box-at13243142 sD006
lem-VPQ-at13243142 : _
lem-VPQ-at13243142 = D006.lem-VPQ-at13243142 sD006
lem-VPQ-at03102132 : _
lem-VPQ-at03102132 = D006.lem-VPQ-at03102132 sD006
lem-tP-at3443 : _
lem-tP-at3443 = D006.lem-tP-at3443 sD006
lem-VPQ-at0410213243 : _
lem-VPQ-at0410213243 = D006.lem-VPQ-at0410213243 sD006
lem-box-tQ-at043043 : _
lem-box-tQ-at043043 = D006.lem-box-tQ-at043043 sD006
lem-tP-at043043 : _
lem-tP-at043043 = D006.lem-tP-at043043 sD006
lem-box-tQ-at0330 : _
lem-box-tQ-at0330 = D006.lem-box-tQ-at0330 sD006
lem-VPQ-at04203243 : _
lem-VPQ-at04203243 = D006.lem-VPQ-at04203243 sD006
lem-tP-at0330 : _
lem-tP-at0330 = D006.lem-tP-at0330 sD006
lem-box-tQ-at0310243142 : _
lem-box-tQ-at0310243142 = D006.lem-box-tQ-at0310243142 sD006
lem-tP-at0314203142 : _
lem-tP-at0314203142 = D006.lem-tP-at0314203142 sD006
lem-tP-at0310243142 : _
lem-tP-at0310243142 = D006.lem-tP-at0310243142 sD006
lem-CXbc-box-at04203243 : _
lem-CXbc-box-at04203243 = D006.lem-CXbc-box-at04203243 sD006
lem-CXcb-box-at04203243 : _
lem-CXcb-box-at04203243 = D006.lem-CXcb-box-at04203243 sD006
lem-CXbc-box-at032032 : _
lem-CXbc-box-at032032 = D006.lem-CXbc-box-at032032 sD006
lem-CXcb-box-at032032 : _
lem-CXcb-box-at032032 = D006.lem-CXcb-box-at032032 sD006
lem-box-tQ-at0214203143 : _
lem-box-tQ-at0214203143 = D006.lem-box-tQ-at0214203143 sD006
lem-box-tQ-at0214213043 : _
lem-box-tQ-at0214213043 = D006.lem-box-tQ-at0214213043 sD006
lem-tP-at0214213043 : _
lem-tP-at0214213043 = D006.lem-tP-at0214213043 sD006
lem-box-tQ-at0210233441 : _
lem-box-tQ-at0210233441 = D006.lem-box-tQ-at0210233441 sD006
lem-tP-at0210233441 : _
lem-tP-at0210233441 = D006.lem-tP-at0210233441 sD006
lem-tP-at12233441 : _
lem-tP-at12233441 = D006.lem-tP-at12233441 sD006
lem-box-tQ-at14213243 : _
lem-box-tQ-at14213243 = D006.lem-box-tQ-at14213243 sD006
lem-box-tQ-at143143 : _
lem-box-tQ-at143143 = D006.lem-box-tQ-at143143 sD006
lem-tP-at143143 : _
lem-tP-at143143 = D006.lem-tP-at143143 sD006
lem-tP-at233442 : _
lem-tP-at233442 = D006.lem-tP-at233442 sD006
lem-VPQ-at0210213443 : _
lem-VPQ-at0210213443 = D006.lem-VPQ-at0210213443 sD006
lem-P-box-at14233241 : _
lem-P-box-at14233241 = D006.lem-P-box-at14233241 sD006
lem-VPQ-at14233241 : _
lem-VPQ-at14233241 = D006.lem-VPQ-at14233241 sD006
lem-box-tQ-at12213443 : _
lem-box-tQ-at12213443 = D006.lem-box-tQ-at12213443 sD006
lem-tP-at12213443 : _
lem-tP-at12213443 = D006.lem-tP-at12213443 sD006
lem-box-tQ-at0314213042 : _
lem-box-tQ-at0314213042 = D006.lem-box-tQ-at0314213042 sD006
lem-tP-at0213203441 : _
lem-tP-at0213203441 = D006.lem-tP-at0213203441 sD006
lem-box-tQ-at0314203142 : _
lem-box-tQ-at0314203142 = D006.lem-box-tQ-at0314203142 sD006
lem-tP-at0314213042 : _
lem-tP-at0314213042 = D006.lem-tP-at0314213042 sD006
lem-P-box-at032032 : _
lem-P-box-at032032 = D006.lem-P-box-at032032 sD006
lem-VPQ-at032032 : _
lem-VPQ-at032032 = D006.lem-VPQ-at032032 sD006
lem-box-tQ-at0312243140 : _
lem-box-tQ-at0312243140 = D006.lem-box-tQ-at0312243140 sD006
lem-box-tQ-at033440 : _
lem-box-tQ-at033440 = D006.lem-box-tQ-at033440 sD006
lem-box-tQ-at0312213440 : _
lem-box-tQ-at0312213440 = D006.lem-box-tQ-at0312213440 sD006
lem-tP-at0312243140 : _
lem-tP-at0312243140 = D006.lem-tP-at0312243140 sD006
lem-box-tQ-at022330 : _
lem-box-tQ-at022330 = D006.lem-box-tQ-at022330 sD006
lem-nat-SWbc-at022330 : _
lem-nat-SWbc-at022330 = D006.lem-nat-SWbc-at022330 sD006
lem-P-box-at0220 : _
lem-P-box-at0220 = D006.lem-P-box-at0220 sD006
lem-VPQ-at0220 : _
lem-VPQ-at0220 = D006.lem-VPQ-at0220 sD006
lem-CXbc-box-at0213243140 : _
lem-CXbc-box-at0213243140 = D006.lem-CXbc-box-at0213243140 sD006
lem-CXcb-box-at0213243140 : _
lem-CXcb-box-at0213243140 = D006.lem-CXcb-box-at0213243140 sD006
sD009 : SD009
sD009 = lem-CXbc-box-at032032 ∷ᵃ lem-CXbc-box-at04203243 ∷ᵃ lem-CXbc-box-at13243142 ∷ᵃ lem-CXbc-box-at13243241 ∷ᵃ lem-CXbc-box-at14233142 ∷ᵃ lem-CXcb-box-at032032 ∷ᵃ lem-CXcb-box-at04203243 ∷ᵃ lem-CXcb-box-at13243142 ∷ᵃ lem-CXcb-box-at13243241 ∷ᵃ lem-CXcb-box-at14233142 ∷ᵃ lem-VPQ-at021021 ∷ᵃ lem-VPQ-at03102132 ∷ᵃ lem-VPQ-at0410213243 ∷ᵃ lem-VPQ-at04203243 ∷ᵃ lem-VPQ-at13243142 ∷ᵃ lem-VPQ-at13243241 ∷ᵃ lem-VPQ-at14233142 ∷ᵃ lem-box-tQ ∷ᵃ lem-box-tQ-at0210243143 ∷ᵃ lem-box-tQ-at0214203143 ∷ᵃ lem-box-tQ-at0214213043 ∷ᵃ lem-box-tQ-at0310243142 ∷ᵃ lem-box-tQ-at0330 ∷ᵃ lem-box-tQ-at043043 ∷ᵃ lem-box-tQ-at1221 ∷ᵃ lem-box-tQ-at122331 ∷ᵃ lem-box-tQ-at12243143 ∷ᵃ lem-box-tQ-at122441 ∷ᵃ lem-box-tQ-at132132 ∷ᵃ lem-box-tQ-at13213442 ∷ᵃ lem-box-tQ-at1331 ∷ᵃ lem-box-tQ-at133441 ∷ᵃ lem-box-tQ-at2332 ∷ᵃ lem-box-tQ-at243243 ∷ᵃ lem-box-tQ-at3443 ∷ᵃ lem-tP ∷ᵃ lem-tP-at0110 ∷ᵃ lem-tP-at0210243143 ∷ᵃ lem-tP-at0214213043 ∷ᵃ lem-tP-at0310243142 ∷ᵃ lem-tP-at0314203142 ∷ᵃ lem-tP-at0330 ∷ᵃ lem-tP-at043043 ∷ᵃ lem-tP-at1221 ∷ᵃ lem-tP-at122331 ∷ᵃ lem-tP-at122441 ∷ᵃ lem-tP-at132132 ∷ᵃ lem-tP-at13213442 ∷ᵃ lem-tP-at1331 ∷ᵃ lem-tP-at2332 ∷ᵃ lem-tP-at243243 ∷ᵃ lem-tP-at3443 ∷ᵃ nil
lem-VPQ : _
lem-VPQ = D009.lem-VPQ sD009
lem-t-cP : _
lem-t-cP = D009.lem-t-cP sD009
lem-VPQ-at0210243143 : _
lem-VPQ-at0210243143 = D009.lem-VPQ-at0210243143 sD009
lem-t-cP-at0210243143 : _
lem-t-cP-at0210243143 = D009.lem-t-cP-at0210243143 sD009
lem-VPQ-at243243 : _
lem-VPQ-at243243 = D009.lem-VPQ-at243243 sD009
lem-t-cP-at243243 : _
lem-t-cP-at243243 = D009.lem-t-cP-at243243 sD009
lem-VPQ-at122441 : _
lem-VPQ-at122441 = D009.lem-VPQ-at122441 sD009
lem-t-cP-at122441 : _
lem-t-cP-at122441 = D009.lem-t-cP-at122441 sD009
lem-CXcb-box : _
lem-CXcb-box = D009.lem-CXcb-box sD009
lem-CXbc-box : _
lem-CXbc-box = D009.lem-CXbc-box sD009
lem-P-box : _
lem-P-box = D009.lem-P-box sD009
lem-CXbc-box-at1221 : _
lem-CXbc-box-at1221 = D009.lem-CXbc-box-at1221 sD009
lem-CXcb-box-at1221 : _
lem-CXcb-box-at1221 = D009.lem-CXcb-box-at1221 sD009
lem-P-box-at1221 : _
lem-P-box-at1221 = D009.lem-P-box-at1221 sD009
lem-VPQ-at1221 : _
lem-VPQ-at1221 = D009.lem-VPQ-at1221 sD009
lem-P-box-at2332 : _
lem-P-box-at2332 = D009.lem-P-box-at2332 sD009
lem-VPQ-at2332 : _
lem-VPQ-at2332 = D009.lem-VPQ-at2332 sD009
lem-SWbc-box-at13243142 : _
lem-SWbc-box-at13243142 = D009.lem-SWbc-box-at13243142 sD009
lem-P-box-at122331 : _
lem-P-box-at122331 = D009.lem-P-box-at122331 sD009
lem-VPQ-at122331 : _
lem-VPQ-at122331 = D009.lem-VPQ-at122331 sD009
lem-SWbc-box-at13243241 : _
lem-SWbc-box-at13243241 = D009.lem-SWbc-box-at13243241 sD009
lem-P-box-at132132 : _
lem-P-box-at132132 = D009.lem-P-box-at132132 sD009
lem-VPQ-at132132 : _
lem-VPQ-at132132 = D009.lem-VPQ-at132132 sD009
lem-CXbc-box-at12243143 : _
lem-CXbc-box-at12243143 = D009.lem-CXbc-box-at12243143 sD009
lem-CXcb-box-at12243143 : _
lem-CXcb-box-at12243143 = D009.lem-CXcb-box-at12243143 sD009
lem-SWbc-box-at14233142 : _
lem-SWbc-box-at14233142 = D009.lem-SWbc-box-at14233142 sD009
lem-QVQ-at14233142 : _
lem-QVQ-at14233142 = D009.lem-QVQ-at14233142 sD009
lem-P-box-at13213442 : _
lem-P-box-at13213442 = D009.lem-P-box-at13213442 sD009
lem-VPQ-at13213442 : _
lem-VPQ-at13213442 = D009.lem-VPQ-at13213442 sD009
lem-P-box-at1331 : _
lem-P-box-at1331 = D009.lem-P-box-at1331 sD009
lem-VPQ-at1331 : _
lem-VPQ-at1331 = D009.lem-VPQ-at1331 sD009
lem-Su-box : _
lem-Su-box = D009.lem-Su-box sD009
lem-Sdu-box : _
lem-Sdu-box = D009.lem-Sdu-box sD009
lem-CSu-box-1 : _
lem-CSu-box-1 = D009.lem-CSu-box-1 sD009
lem-CSdu-box-1 : _
lem-CSdu-box-1 = D009.lem-CSdu-box-1 sD009
lem-CSu-box-2 : _
lem-CSu-box-2 = D009.lem-CSu-box-2 sD009
lem-CSdu-box-2 : _
lem-CSdu-box-2 = D009.lem-CSdu-box-2 sD009
lem-VPQ-at0110 : _
lem-VPQ-at0110 = D009.lem-VPQ-at0110 sD009
lem-CXbc-box-at133441 : _
lem-CXbc-box-at133441 = D009.lem-CXbc-box-at133441 sD009
lem-CXcb-box-at133441 : _
lem-CXcb-box-at133441 = D009.lem-CXcb-box-at133441 sD009
lem-QVQ-at13243241 : _
lem-QVQ-at13243241 = D009.lem-QVQ-at13243241 sD009
lem-QVQ-at021021 : _
lem-QVQ-at021021 = D009.lem-QVQ-at021021 sD009
lem-CXbc-box-at13213442 : _
lem-CXbc-box-at13213442 = D009.lem-CXbc-box-at13213442 sD009
lem-CXcb-box-at13213442 : _
lem-CXcb-box-at13213442 = D009.lem-CXcb-box-at13213442 sD009
lem-QVQ-at13243142 : _
lem-QVQ-at13243142 = D009.lem-QVQ-at13243142 sD009
lem-QVQ-at03102132 : _
lem-QVQ-at03102132 = D009.lem-QVQ-at03102132 sD009
lem-P-box-at3443 : _
lem-P-box-at3443 = D009.lem-P-box-at3443 sD009
lem-VPQ-at3443 : _
lem-VPQ-at3443 = D009.lem-VPQ-at3443 sD009
lem-QVQ-at0410213243 : _
lem-QVQ-at0410213243 = D009.lem-QVQ-at0410213243 sD009
lem-VPQ-at043043 : _
lem-VPQ-at043043 = D009.lem-VPQ-at043043 sD009
lem-CXbc-box-at043043 : _
lem-CXbc-box-at043043 = D009.lem-CXbc-box-at043043 sD009
lem-CXcb-box-at043043 : _
lem-CXcb-box-at043043 = D009.lem-CXcb-box-at043043 sD009
lem-QVQ-at04203243 : _
lem-QVQ-at04203243 = D009.lem-QVQ-at04203243 sD009
lem-P-box-at0330 : _
lem-P-box-at0330 = D009.lem-P-box-at0330 sD009
lem-VPQ-at0330 : _
lem-VPQ-at0330 = D009.lem-VPQ-at0330 sD009
lem-VPQ-at0314203142 : _
lem-VPQ-at0314203142 = D009.lem-VPQ-at0314203142 sD009
lem-P-box-at0310243142 : _
lem-P-box-at0310243142 = D009.lem-P-box-at0310243142 sD009
lem-VPQ-at0310243142 : _
lem-VPQ-at0310243142 = D009.lem-VPQ-at0310243142 sD009
lem-SWbc-box-at04203243 : _
lem-SWbc-box-at04203243 = D009.lem-SWbc-box-at04203243 sD009
lem-SWbc-box-at032032 : _
lem-SWbc-box-at032032 = D009.lem-SWbc-box-at032032 sD009
lem-t-cP-at043043 : _
lem-t-cP-at043043 = D009.lem-t-cP-at043043 sD009
lem-CXbc-box-at0330 : _
lem-CXbc-box-at0330 = D009.lem-CXbc-box-at0330 sD009
lem-CXcb-box-at0330 : _
lem-CXcb-box-at0330 = D009.lem-CXcb-box-at0330 sD009
lem-CSdu-box-2-at243243 : _
lem-CSdu-box-2-at243243 = D009.lem-CSdu-box-2-at243243 sD009
lem-Su-box-at243243 : _
lem-Su-box-at243243 = D009.lem-Su-box-at243243 sD009
lem-CSdu-box-2-at122441 : _
lem-CSdu-box-2-at122441 = D009.lem-CSdu-box-2-at122441 sD009
lem-Su-box-at122441 : _
lem-Su-box-at122441 = D009.lem-Su-box-at122441 sD009
lem-CSdu-box-2-at0210243143 : _
lem-CSdu-box-2-at0210243143 = D009.lem-CSdu-box-2-at0210243143 sD009
lem-Su-box-at0210243143 : _
lem-Su-box-at0210243143 = D009.lem-Su-box-at0210243143 sD009
lem-CSu-box-2-at243243 : _
lem-CSu-box-2-at243243 = D009.lem-CSu-box-2-at243243 sD009
lem-CSu-box-2-at122441 : _
lem-CSu-box-2-at122441 = D009.lem-CSu-box-2-at122441 sD009
lem-CXbc-box-at0214203143 : _
lem-CXbc-box-at0214203143 = D009.lem-CXbc-box-at0214203143 sD009
lem-CXcb-box-at0214203143 : _
lem-CXcb-box-at0214203143 = D009.lem-CXcb-box-at0214203143 sD009
lem-P-box-at0214213043 : _
lem-P-box-at0214213043 = D009.lem-P-box-at0214213043 sD009
sD010 : SD010
sD010 = lem-CXbc-box-at0213243140 ∷ᵃ lem-CXcb-box-at0213243140 ∷ᵃ lem-VPQ-at0210213443 ∷ᵃ lem-VPQ-at0220 ∷ᵃ lem-VPQ-at032032 ∷ᵃ lem-VPQ-at14233241 ∷ᵃ lem-box-tQ-at0210233441 ∷ᵃ lem-box-tQ-at0210243143 ∷ᵃ lem-box-tQ-at0214203143 ∷ᵃ lem-box-tQ-at0214213043 ∷ᵃ lem-box-tQ-at022330 ∷ᵃ lem-box-tQ-at0312213440 ∷ᵃ lem-box-tQ-at0312243140 ∷ᵃ lem-box-tQ-at0314203142 ∷ᵃ lem-box-tQ-at0314213042 ∷ᵃ lem-box-tQ-at122331 ∷ᵃ lem-box-tQ-at12233441 ∷ᵃ lem-box-tQ-at122441 ∷ᵃ lem-box-tQ-at132132 ∷ᵃ lem-box-tQ-at1331 ∷ᵃ lem-box-tQ-at14213243 ∷ᵃ lem-box-tQ-at143143 ∷ᵃ lem-box-tQ-at1441 ∷ᵃ lem-box-tQ-at2332 ∷ᵃ lem-box-tQ-at243243 ∷ᵃ lem-tP-at0210233441 ∷ᵃ lem-tP-at0210243143 ∷ᵃ lem-tP-at0213203441 ∷ᵃ lem-tP-at0214213043 ∷ᵃ lem-tP-at0312243140 ∷ᵃ lem-tP-at0314213042 ∷ᵃ lem-tP-at12213443 ∷ᵃ lem-tP-at12233441 ∷ᵃ lem-tP-at122441 ∷ᵃ lem-tP-at143143 ∷ᵃ lem-tP-at233442 ∷ᵃ lem-tP-at243243 ∷ᵃ lem-CXbc-box-at0220 ∷ᵃ lem-CXbc-box-at03102132 ∷ᵃ lem-CXcb-box-at0220 ∷ᵃ lem-CXcb-box-at03102132 ∷ᵃ lem-VPQ-at0213243140 ∷ᵃ lem-box-tQ-at0213213440 ∷ᵃ lem-box-tQ-at02233440 ∷ᵃ lem-box-tQ-at022440 ∷ᵃ lem-tP-at0214203143 ∷ᵃ lem-tP-at022330 ∷ᵃ lem-tP-at022440 ∷ᵃ lem-tP-at14213243 ∷ᵃ nil
lem-VPQ-at0214213043 : _
lem-VPQ-at0214213043 = D010.lem-VPQ-at0214213043 sD010
lem-VPQ-at0210233441 : _
lem-VPQ-at0210233441 = D010.lem-VPQ-at0210233441 sD010
lem-CXbc-box-at122441 : _
lem-CXbc-box-at122441 = D010.lem-CXbc-box-at122441 sD010
lem-CXcb-box-at122441 : _
lem-CXcb-box-at122441 = D010.lem-CXcb-box-at122441 sD010
lem-VPQ-at12233441 : _
lem-VPQ-at12233441 = D010.lem-VPQ-at12233441 sD010
lem-CSu-box-2-at0210243143 : _
lem-CSu-box-2-at0210243143 = D010.lem-CSu-box-2-at0210243143 sD010
lem-CXbc-box-at14213243 : _
lem-CXbc-box-at14213243 = D010.lem-CXbc-box-at14213243 sD010
lem-CXcb-box-at14213243 : _
lem-CXcb-box-at14213243 = D010.lem-CXcb-box-at14213243 sD010
lem-P-box-at143143 : _
lem-P-box-at143143 = D010.lem-P-box-at143143 sD010
lem-VPQ-at143143 : _
lem-VPQ-at143143 = D010.lem-VPQ-at143143 sD010
lem-VPQ-at233442 : _
lem-VPQ-at233442 = D010.lem-VPQ-at233442 sD010
lem-CXbc-box-at0210243143 : _
lem-CXbc-box-at0210243143 = D010.lem-CXbc-box-at0210243143 sD010
lem-CXcb-box-at0210243143 : _
lem-CXcb-box-at0210243143 = D010.lem-CXcb-box-at0210243143 sD010
lem-QVQ-at0210213443 : _
lem-QVQ-at0210213443 = D010.lem-QVQ-at0210213443 sD010
lem-CXbc-box-at243243 : _
lem-CXbc-box-at243243 = D010.lem-CXbc-box-at243243 sD010
lem-CXcb-box-at243243 : _
lem-CXcb-box-at243243 = D010.lem-CXcb-box-at243243 sD010
lem-CXbc-box-at1441 : _
lem-CXbc-box-at1441 = D010.lem-CXbc-box-at1441 sD010
lem-CXcb-box-at1441 : _
lem-CXcb-box-at1441 = D010.lem-CXcb-box-at1441 sD010
lem-QVQ-at14233241 : _
lem-QVQ-at14233241 = D010.lem-QVQ-at14233241 sD010
lem-VPQ-at12213443 : _
lem-VPQ-at12213443 = D010.lem-VPQ-at12213443 sD010
lem-CXbc-box-at0314213042 : _
lem-CXbc-box-at0314213042 = D010.lem-CXbc-box-at0314213042 sD010
lem-CXcb-box-at0314213042 : _
lem-CXcb-box-at0314213042 = D010.lem-CXcb-box-at0314213042 sD010
lem-VPQ-at0213203441 : _
lem-VPQ-at0213203441 = D010.lem-VPQ-at0213203441 sD010
lem-P-box-at0210233441 : _
lem-P-box-at0210233441 = D010.lem-P-box-at0210233441 sD010
lem-CXbc-box-at0314203142 : _
lem-CXbc-box-at0314203142 = D010.lem-CXbc-box-at0314203142 sD010
lem-CXcb-box-at0314203142 : _
lem-CXcb-box-at0314203142 = D010.lem-CXcb-box-at0314203142 sD010
lem-VPQ-at0314213042 : _
lem-VPQ-at0314213042 = D010.lem-VPQ-at0314213042 sD010
lem-t-cP-at0314213042 : _
lem-t-cP-at0314213042 = D010.lem-t-cP-at0314213042 sD010
lem-CXbc-box-at0214213043 : _
lem-CXbc-box-at0214213043 = D010.lem-CXbc-box-at0214213043 sD010
lem-CXcb-box-at0214213043 : _
lem-CXcb-box-at0214213043 = D010.lem-CXcb-box-at0214213043 sD010
lem-P-box-at243243 : _
lem-P-box-at243243 = D010.lem-P-box-at243243 sD010
lem-CXbc-box-at1331 : _
lem-CXbc-box-at1331 = D010.lem-CXbc-box-at1331 sD010
lem-CXcb-box-at1331 : _
lem-CXcb-box-at1331 = D010.lem-CXcb-box-at1331 sD010
lem-QVQ-at032032 : _
lem-QVQ-at032032 = D010.lem-QVQ-at032032 sD010
lem-CXbc-box-at0312243140 : _
lem-CXbc-box-at0312243140 = D010.lem-CXbc-box-at0312243140 sD010
lem-CXcb-box-at0312243140 : _
lem-CXcb-box-at0312243140 = D010.lem-CXcb-box-at0312243140 sD010
lem-CXbc-box-at0312213440 : _
lem-CXbc-box-at0312213440 = D010.lem-CXbc-box-at0312213440 sD010
lem-CXcb-box-at0312213440 : _
lem-CXcb-box-at0312213440 = D010.lem-CXcb-box-at0312213440 sD010
lem-P-box-at0312243140 : _
lem-P-box-at0312243140 = D010.lem-P-box-at0312243140 sD010
lem-VPQ-at0312243140 : _
lem-VPQ-at0312243140 = D010.lem-VPQ-at0312243140 sD010
lem-CXbc-box-at132132 : _
lem-CXbc-box-at132132 = D010.lem-CXbc-box-at132132 sD010
lem-CXcb-box-at132132 : _
lem-CXcb-box-at132132 = D010.lem-CXcb-box-at132132 sD010
lem-P-box-at0210243143 : _
lem-P-box-at0210243143 = D010.lem-P-box-at0210243143 sD010
lem-CXbc-box-at022330 : _
lem-CXbc-box-at022330 = D010.lem-CXbc-box-at022330 sD010
lem-CXcb-box-at022330 : _
lem-CXcb-box-at022330 = D010.lem-CXcb-box-at022330 sD010
lem-QVQ-at0220 : _
lem-QVQ-at0220 = D010.lem-QVQ-at0220 sD010
lem-SWbc-box-at0213243140 : _
lem-SWbc-box-at0213243140 = D010.lem-SWbc-box-at0213243140 sD010
lem-CXbc-box-at0213213440 : _
lem-CXbc-box-at0213213440 = D010.lem-CXbc-box-at0213213440 sD010
lem-CXcb-box-at0213213440 : _
lem-CXcb-box-at0213213440 = D010.lem-CXcb-box-at0213213440 sD010
lem-QVQ-at0213243140 : _
lem-QVQ-at0213243140 = D010.lem-QVQ-at0213243140 sD010
lem-SWbc-box-at0220 : _
lem-SWbc-box-at0220 = D010.lem-SWbc-box-at0220 sD010
lem-P-box-at022330 : _
lem-P-box-at022330 = D010.lem-P-box-at022330 sD010
lem-VPQ-at022330 : _
lem-VPQ-at022330 = D010.lem-VPQ-at022330 sD010
lem-CXbc-box-at122331 : _
lem-CXbc-box-at122331 = D010.lem-CXbc-box-at122331 sD010
lem-CXcb-box-at122331 : _
lem-CXcb-box-at122331 = D010.lem-CXcb-box-at122331 sD010
lem-P-box-at14213243 : _
lem-P-box-at14213243 = D010.lem-P-box-at14213243 sD010
lem-VPQ-at14213243 : _
lem-VPQ-at14213243 = D010.lem-VPQ-at14213243 sD010
lem-CXbc-box-at12233441 : _
lem-CXbc-box-at12233441 = D010.lem-CXbc-box-at12233441 sD010
lem-CXcb-box-at12233441 : _
lem-CXcb-box-at12233441 = D010.lem-CXcb-box-at12233441 sD010
lem-P-box-at12233441 : _
lem-P-box-at12233441 = D010.lem-P-box-at12233441 sD010
lem-P-box-at122441 : _
lem-P-box-at122441 = D010.lem-P-box-at122441 sD010
lem-CXbc-box-at2332 : _
lem-CXbc-box-at2332 = D010.lem-CXbc-box-at2332 sD010
lem-CXcb-box-at2332 : _
lem-CXcb-box-at2332 = D010.lem-CXcb-box-at2332 sD010
lem-SWbc-box-at03102132 : _
lem-SWbc-box-at03102132 = D010.lem-SWbc-box-at03102132 sD010
lem-P-box-at0214203143 : _
lem-P-box-at0214203143 = D010.lem-P-box-at0214203143 sD010
lem-VPQ-at0214203143 : _
lem-VPQ-at0214203143 = D010.lem-VPQ-at0214203143 sD010
lem-CXbc-box-at02233440 : _
lem-CXbc-box-at02233440 = D010.lem-CXbc-box-at02233440 sD010
lem-CXcb-box-at02233440 : _
lem-CXcb-box-at02233440 = D010.lem-CXcb-box-at02233440 sD010
lem-VPQ-at022440 : _
lem-VPQ-at022440 = D010.lem-VPQ-at022440 sD010
lem-CXbc-box-at022440 : _
lem-CXbc-box-at022440 = D010.lem-CXbc-box-at022440 sD010
sD011 : SD011
sD011 = lem-box-tQ ∷ᵃ lem-box-tQ-at0210233441 ∷ᵃ lem-box-tQ-at0310243142 ∷ᵃ lem-box-tQ-at0314203142 ∷ᵃ lem-box-tQ-at0314213042 ∷ᵃ lem-box-tQ-at033440 ∷ᵃ lem-box-tQ-at12213443 ∷ᵃ lem-box-tQ-at143143 ∷ᵃ lem-box-tQ-at1441 ∷ᵃ lem-box-tQ-at233442 ∷ᵃ lem-box-tQ-at2442 ∷ᵃ lem-box-tQ-at3443 ∷ᵃ lem-tP-at0310243142 ∷ᵃ lem-tP-at0314203142 ∷ᵃ lem-tP-at0314213042 ∷ᵃ lem-tP-at12213443 ∷ᵃ lem-tP-at233442 ∷ᵃ lem-CXbc-box-at0310213442 ∷ᵃ lem-CXbc-box-at14233241 ∷ᵃ lem-CXcb-box-at0310213442 ∷ᵃ lem-CXcb-box-at14233241 ∷ᵃ lem-box-tQ-at02102441 ∷ᵃ lem-box-tQ-at02142041 ∷ᵃ lem-box-tQ-at02233440 ∷ᵃ lem-box-tQ-at022440 ∷ᵃ lem-box-tQ-at0310243241 ∷ᵃ lem-box-tQ-at031031 ∷ᵃ lem-box-tQ-at03103441 ∷ᵃ lem-box-tQ-at0312203441 ∷ᵃ lem-box-tQ-at0312243041 ∷ᵃ lem-box-tQ-at0314213240 ∷ᵃ lem-box-tQ-at03143041 ∷ᵃ lem-box-tQ-at03143140 ∷ᵃ lem-box-tQ-at03243240 ∷ᵃ lem-tP-at02102441 ∷ᵃ lem-tP-at02233440 ∷ᵃ lem-tP-at0310243241 ∷ᵃ lem-tP-at031031 ∷ᵃ lem-tP-at03103441 ∷ᵃ lem-tP-at0312203441 ∷ᵃ lem-tP-at0312243041 ∷ᵃ lem-tP-at0314213240 ∷ᵃ lem-tP-at03143140 ∷ᵃ lem-tP-at03243240 ∷ᵃ lem-tP-at033440 ∷ᵃ lem-tP-at12243143 ∷ᵃ lem-tP-at1441 ∷ᵃ lem-tP-at2442 ∷ᵃ nil
lem-CXcb-box-at022440 : _
lem-CXcb-box-at022440 = D011.lem-CXcb-box-at022440 sD011
lem-P-box-at02233440 : _
lem-P-box-at02233440 = D011.lem-P-box-at02233440 sD011
lem-VPQ-at02233440 : _
lem-VPQ-at02233440 = D011.lem-VPQ-at02233440 sD011
lem-P-box-at1441 : _
lem-P-box-at1441 = D011.lem-P-box-at1441 sD011
lem-VPQ-at1441 : _
lem-VPQ-at1441 = D011.lem-VPQ-at1441 sD011
lem-CXbc-box-at0210233441 : _
lem-CXbc-box-at0210233441 = D011.lem-CXbc-box-at0210233441 sD011
lem-CXcb-box-at0210233441 : _
lem-CXcb-box-at0210233441 = D011.lem-CXcb-box-at0210233441 sD011
lem-VPQ-at02102441 : _
lem-VPQ-at02102441 = D011.lem-VPQ-at02102441 sD011
lem-CXbc-box-at02102441 : _
lem-CXbc-box-at02102441 = D011.lem-CXbc-box-at02102441 sD011
lem-CXcb-box-at02102441 : _
lem-CXcb-box-at02102441 = D011.lem-CXcb-box-at02102441 sD011
lem-CXbc-box-at233442 : _
lem-CXbc-box-at233442 = D011.lem-CXbc-box-at233442 sD011
lem-CXcb-box-at233442 : _
lem-CXcb-box-at233442 = D011.lem-CXcb-box-at233442 sD011
lem-VPQ-at2442 : _
lem-VPQ-at2442 = D011.lem-VPQ-at2442 sD011
lem-CXbc-box-at2442 : _
lem-CXbc-box-at2442 = D011.lem-CXbc-box-at2442 sD011
lem-CXcb-box-at2442 : _
lem-CXcb-box-at2442 = D011.lem-CXcb-box-at2442 sD011
lem-P-box-at233442 : _
lem-P-box-at233442 = D011.lem-P-box-at233442 sD011
lem-CXbc-box-at143143 : _
lem-CXbc-box-at143143 = D011.lem-CXbc-box-at143143 sD011
lem-CXcb-box-at143143 : _
lem-CXcb-box-at143143 = D011.lem-CXcb-box-at143143 sD011
lem-CXbc-box-at12213443 : _
lem-CXbc-box-at12213443 = D011.lem-CXbc-box-at12213443 sD011
lem-CXcb-box-at12213443 : _
lem-CXcb-box-at12213443 = D011.lem-CXcb-box-at12213443 sD011
lem-VPQ-at12243143 : _
lem-VPQ-at12243143 = D011.lem-VPQ-at12243143 sD011
lem-P-box-at12213443 : _
lem-P-box-at12213443 = D011.lem-P-box-at12213443 sD011
lem-SWbc-box-at14233241 : _
lem-SWbc-box-at14233241 = D011.lem-SWbc-box-at14233241 sD011
lem-CXbc-box-at03143140 : _
lem-CXbc-box-at03143140 = D011.lem-CXbc-box-at03143140 sD011
lem-CXcb-box-at03143140 : _
lem-CXcb-box-at03143140 = D011.lem-CXcb-box-at03143140 sD011
lem-VPQ-at0314213240 : _
lem-VPQ-at0314213240 = D011.lem-VPQ-at0314213240 sD011
lem-CXbc-box-at0314213240 : _
lem-CXbc-box-at0314213240 = D011.lem-CXbc-box-at0314213240 sD011
lem-CXcb-box-at0314213240 : _
lem-CXcb-box-at0314213240 = D011.lem-CXcb-box-at0314213240 sD011
lem-VPQ-at03143140 : _
lem-VPQ-at03143140 = D011.lem-VPQ-at03143140 sD011
lem-t-cP-at03143140 : _
lem-t-cP-at03143140 = D011.lem-t-cP-at03143140 sD011
lem-VPQ-at03243240 : _
lem-VPQ-at03243240 = D011.lem-VPQ-at03243240 sD011
lem-P-box-at0314203142 : _
lem-P-box-at0314203142 = D011.lem-P-box-at0314203142 sD011
lem-CXbc-box-at033440 : _
lem-CXbc-box-at033440 = D011.lem-CXbc-box-at033440 sD011
lem-CXcb-box-at033440 : _
lem-CXcb-box-at033440 = D011.lem-CXcb-box-at033440 sD011
lem-t-cP-at03243240 : _
lem-t-cP-at03243240 = D011.lem-t-cP-at03243240 sD011
lem-CXbc-box-at03243240 : _
lem-CXbc-box-at03243240 = D011.lem-CXbc-box-at03243240 sD011
lem-CXcb-box-at03243240 : _
lem-CXcb-box-at03243240 = D011.lem-CXcb-box-at03243240 sD011
lem-VPQ-at033440 : _
lem-VPQ-at033440 = D011.lem-VPQ-at033440 sD011
lem-P-box-at033440 : _
lem-P-box-at033440 = D011.lem-P-box-at033440 sD011
lem-t-cP-at0310243142 : _
lem-t-cP-at0310243142 = D011.lem-t-cP-at0310243142 sD011
lem-P-box-at0314213042 : _
lem-P-box-at0314213042 = D011.lem-P-box-at0314213042 sD011
lem-CXbc-box-at03103441 : _
lem-CXbc-box-at03103441 = D011.lem-CXbc-box-at03103441 sD011
lem-CXcb-box-at03103441 : _
lem-CXcb-box-at03103441 = D011.lem-CXcb-box-at03103441 sD011
lem-VPQ-at0310243241 : _
lem-VPQ-at0310243241 = D011.lem-VPQ-at0310243241 sD011
lem-CXbc-box-at0310243241 : _
lem-CXbc-box-at0310243241 = D011.lem-CXbc-box-at0310243241 sD011
lem-CXcb-box-at0310243241 : _
lem-CXcb-box-at0310243241 = D011.lem-CXcb-box-at0310243241 sD011
lem-P-box-at03103441 : _
lem-P-box-at03103441 = D011.lem-P-box-at03103441 sD011
lem-VPQ-at03103441 : _
lem-VPQ-at03103441 = D011.lem-VPQ-at03103441 sD011
lem-CXbc-box-at0310243142 : _
lem-CXbc-box-at0310243142 = D011.lem-CXbc-box-at0310243142 sD011
lem-CXcb-box-at0310243142 : _
lem-CXcb-box-at0310243142 = D011.lem-CXcb-box-at0310243142 sD011
lem-SWbc-box-at0310213442 : _
lem-SWbc-box-at0310213442 = D011.lem-SWbc-box-at0310213442 sD011
lem-P-box-at0314213240 : _
lem-P-box-at0314213240 = D011.lem-P-box-at0314213240 sD011
lem-CXbc-box-at0312203441 : _
lem-CXbc-box-at0312203441 = D011.lem-CXbc-box-at0312203441 sD011
lem-CXcb-box-at0312203441 : _
lem-CXcb-box-at0312203441 = D011.lem-CXcb-box-at0312203441 sD011
lem-VPQ-at0312243041 : _
lem-VPQ-at0312243041 = D011.lem-VPQ-at0312243041 sD011
lem-CXbc-box-at0312243041 : _
lem-CXbc-box-at0312243041 = D011.lem-CXbc-box-at0312243041 sD011
lem-CXcb-box-at0312243041 : _
lem-CXcb-box-at0312243041 = D011.lem-CXcb-box-at0312243041 sD011
lem-P-box-at0312203441 : _
lem-P-box-at0312203441 = D011.lem-P-box-at0312203441 sD011
lem-VPQ-at0312203441 : _
lem-VPQ-at0312203441 = D011.lem-VPQ-at0312203441 sD011
lem-CXbc-box-at3443 : _
lem-CXbc-box-at3443 = D011.lem-CXbc-box-at3443 sD011
lem-CXcb-box-at3443 : _
lem-CXcb-box-at3443 = D011.lem-CXcb-box-at3443 sD011
lem-P-box-at03243240 : _
lem-P-box-at03243240 = D011.lem-P-box-at03243240 sD011
lem-CXbc-box-at031031 : _
lem-CXbc-box-at031031 = D011.lem-CXbc-box-at031031 sD011
lem-CXcb-box-at031031 : _
lem-CXcb-box-at031031 = D011.lem-CXcb-box-at031031 sD011
lem-VPQ-at031031 : _
lem-VPQ-at031031 = D011.lem-VPQ-at031031 sD011
lem-CXbc-box-at03143041 : _
lem-CXbc-box-at03143041 = D011.lem-CXbc-box-at03143041 sD011
lem-CXcb-box-at03143041 : _
lem-CXcb-box-at03143041 = D011.lem-CXcb-box-at03143041 sD011
lem-CXbc-box-at02142041 : _
lem-CXbc-box-at02142041 = D011.lem-CXbc-box-at02142041 sD011
sD008 : SD008
sD008 = lem-box-tQ-at0410213243 ∷ᵃ lem-box-tQ-at04203243 ∷ᵃ lem-tP-at0410213243 ∷ᵃ lem-tP-at04203243 ∷ᵃ lem-cQ-at02142140 ∷ᵃ lem-cQ-at0410233142 ∷ᵃ lem-cQ-at0410233241 ∷ᵃ lem-cQ-at041041 ∷ᵃ lem-cQ-at0412213043 ∷ᵃ lem-cQ-at04122140 ∷ᵃ lem-cQ-at0412233041 ∷ᵃ lem-cQ-at0412233140 ∷ᵃ lem-cQ-at0413203142 ∷ᵃ lem-cQ-at0413203241 ∷ᵃ lem-cQ-at0413213042 ∷ᵃ lem-cQ-at0413213240 ∷ᵃ lem-cQ-at04133140 ∷ᵃ lem-cQ-at04233240 ∷ᵃ lem-cQ-at0440 ∷ᵃ lem-tP-at0310213442 ∷ᵃ nil
lem-P-box-at0410213243 : _
lem-P-box-at0410213243 = D008.lem-P-box-at0410213243 sD008
lem-box-tQ-at0412233041 : _
lem-box-tQ-at0412233041 = D008.lem-box-tQ-at0412233041 sD008
lem-box-tQ-at041041 : _
lem-box-tQ-at041041 = D008.lem-box-tQ-at041041 sD008
lem-box-tQ-at0410233241 : _
lem-box-tQ-at0410233241 = D008.lem-box-tQ-at0410233241 sD008
lem-tP-at0410233241 : _
lem-tP-at0410233241 = D008.lem-tP-at0410233241 sD008
lem-box-tQ-at0412213043 : _
lem-box-tQ-at0412213043 = D008.lem-box-tQ-at0412213043 sD008
lem-tP-at0412213043 : _
lem-tP-at0412213043 = D008.lem-tP-at0412213043 sD008
lem-box-tQ-at0413213240 : _
lem-box-tQ-at0413213240 = D008.lem-box-tQ-at0413213240 sD008
lem-box-tQ-at04233240 : _
lem-box-tQ-at04233240 = D008.lem-box-tQ-at04233240 sD008
lem-box-tQ-at0440 : _
lem-box-tQ-at0440 = D008.lem-box-tQ-at0440 sD008
lem-tP-at0440 : _
lem-tP-at0440 = D008.lem-tP-at0440 sD008
lem-box-tQ-at0413203142 : _
lem-box-tQ-at0413203142 = D008.lem-box-tQ-at0413203142 sD008
lem-tP-at02142140 : _
lem-tP-at02142140 = D008.lem-tP-at02142140 sD008
lem-box-tQ-at0413213042 : _
lem-box-tQ-at0413213042 = D008.lem-box-tQ-at0413213042 sD008
lem-tP-at0413203142 : _
lem-tP-at0413203142 = D008.lem-tP-at0413203142 sD008
lem-tP-at0413213240 : _
lem-tP-at0413213240 = D008.lem-tP-at0413213240 sD008
lem-t-cP-at0310213442 : _
lem-t-cP-at0310213442 = D008.lem-t-cP-at0310213442 sD008
lem-P-box-at04203243 : _
lem-P-box-at04203243 = D008.lem-P-box-at04203243 sD008
lem-box-tQ-at0412233140 : _
lem-box-tQ-at0412233140 = D008.lem-box-tQ-at0412233140 sD008
lem-box-tQ-at0410233142 : _
lem-box-tQ-at0410233142 = D008.lem-box-tQ-at0410233142 sD008
lem-tP-at0410233142 : _
lem-tP-at0410233142 = D008.lem-tP-at0410233142 sD008
lem-box-tQ-at04122140 : _
lem-box-tQ-at04122140 = D008.lem-box-tQ-at04122140 sD008
lem-tP-at0412233140 : _
lem-tP-at0412233140 = D008.lem-tP-at0412233140 sD008
lem-t-cP-at04203243 : _
lem-t-cP-at04203243 = D008.lem-t-cP-at04203243 sD008
lem-box-tQ-at0413203241 : _
lem-box-tQ-at0413203241 = D008.lem-box-tQ-at0413203241 sD008
lem-tP-at0413203241 : _
lem-tP-at0413203241 = D008.lem-tP-at0413203241 sD008
lem-tP-at04122140 : _
lem-tP-at04122140 = D008.lem-tP-at04122140 sD008
lem-CSdu-box-2-at04203243 : _
lem-CSdu-box-2-at04203243 = D008.lem-CSdu-box-2-at04203243 sD008
lem-Su-box-at04203243 : _
lem-Su-box-at04203243 = D008.lem-Su-box-at04203243 sD008
lem-box-tQ-at04133140 : _
lem-box-tQ-at04133140 = D008.lem-box-tQ-at04133140 sD008
sD012 : SD012
sD012 = lem-box-tQ-at033440 ∷ᵃ lem-box-tQ-at2442 ∷ᵃ lem-CXbc-box-at021021 ∷ᵃ lem-CXbc-box-at0210213443 ∷ᵃ lem-CXbc-box-at0214233041 ∷ᵃ lem-CXbc-box-at0410213243 ∷ᵃ lem-CXcb-box-at021021 ∷ᵃ lem-CXcb-box-at0210213443 ∷ᵃ lem-CXcb-box-at0214233041 ∷ᵃ lem-CXcb-box-at0410213243 ∷ᵃ lem-VPQ-at0213243041 ∷ᵃ lem-VPQ-at0214233041 ∷ᵃ lem-VPQ-at0310213442 ∷ᵃ lem-box-tQ-at02102331 ∷ᵃ lem-box-tQ-at02102441 ∷ᵃ lem-box-tQ-at02132031 ∷ᵃ lem-box-tQ-at02132130 ∷ᵃ lem-box-tQ-at02142041 ∷ᵃ lem-box-tQ-at0310243241 ∷ᵃ lem-box-tQ-at031031 ∷ᵃ lem-box-tQ-at03122031 ∷ᵃ lem-box-tQ-at03122130 ∷ᵃ lem-box-tQ-at0312243041 ∷ᵃ lem-box-tQ-at0314203241 ∷ᵃ lem-box-tQ-at03143041 ∷ᵃ lem-box-tQ-at03243042 ∷ᵃ lem-box-tQ-at04103143 ∷ᵃ lem-box-tQ-at04122041 ∷ᵃ lem-box-tQ-at142142 ∷ᵃ lem-tP-at02102331 ∷ᵃ lem-tP-at02102441 ∷ᵃ lem-tP-at02132031 ∷ᵃ lem-tP-at02132130 ∷ᵃ lem-tP-at0214203143 ∷ᵃ lem-tP-at02142041 ∷ᵃ lem-tP-at0310243241 ∷ᵃ lem-tP-at031031 ∷ᵃ lem-tP-at03122031 ∷ᵃ lem-tP-at03122130 ∷ᵃ lem-tP-at0312243041 ∷ᵃ lem-tP-at0314203241 ∷ᵃ lem-tP-at03143041 ∷ᵃ lem-tP-at03243042 ∷ᵃ lem-tP-at033440 ∷ᵃ lem-tP-at04103143 ∷ᵃ lem-tP-at04122041 ∷ᵃ lem-tP-at0412233041 ∷ᵃ lem-tP-at04233042 ∷ᵃ lem-tP-at142142 ∷ᵃ lem-tP-at2442 ∷ᵃ lem-box-tQ-at0410233241 ∷ᵃ lem-box-tQ-at041041 ∷ᵃ lem-box-tQ-at0412233041 ∷ᵃ lem-box-tQ-at0413203142 ∷ᵃ lem-box-tQ-at0413213042 ∷ᵃ lem-box-tQ-at04233240 ∷ᵃ lem-box-tQ-at0440 ∷ᵃ lem-tP-at02142140 ∷ᵃ lem-tP-at0410233241 ∷ᵃ lem-tP-at0412213043 ∷ᵃ lem-tP-at0413203142 ∷ᵃ lem-tP-at0440 ∷ᵃ nil
lem-CXcb-box-at02142041 : _
lem-CXcb-box-at02142041 = D012.lem-CXcb-box-at02142041 sD012
lem-QVQ-at0214233041 : _
lem-QVQ-at0214233041 = D012.lem-QVQ-at0214233041 sD012
lem-CXbc-box-at0314203241 : _
lem-CXbc-box-at0314203241 = D012.lem-CXbc-box-at0314203241 sD012
lem-CXcb-box-at0314203241 : _
lem-CXcb-box-at0314203241 = D012.lem-CXcb-box-at0314203241 sD012
lem-SWbc-box-at0210213443 : _
lem-SWbc-box-at0210213443 = D012.lem-SWbc-box-at0210213443 sD012
lem-SWbc-box-at0214233041 : _
lem-SWbc-box-at0214233041 = D012.lem-SWbc-box-at0214233041 sD012
lem-P-box-at0312243041 : _
lem-P-box-at0312243041 = D012.lem-P-box-at0312243041 sD012
lem-P-box-at02102441 : _
lem-P-box-at02102441 = D012.lem-P-box-at02102441 sD012
lem-CXbc-box-at02132130 : _
lem-CXbc-box-at02132130 = D012.lem-CXbc-box-at02132130 sD012
lem-CXcb-box-at02132130 : _
lem-CXcb-box-at02132130 = D012.lem-CXcb-box-at02132130 sD012
lem-P-box-at03143041 : _
lem-P-box-at03143041 = D012.lem-P-box-at03143041 sD012
lem-VPQ-at03143041 : _
lem-VPQ-at03143041 = D012.lem-VPQ-at03143041 sD012
lem-VPQ-at02132031 : _
lem-VPQ-at02132031 = D012.lem-VPQ-at02132031 sD012
lem-QVQ-at0310213442 : _
lem-QVQ-at0310213442 = D012.lem-QVQ-at0310213442 sD012
lem-CXbc-box-at02132031 : _
lem-CXbc-box-at02132031 = D012.lem-CXbc-box-at02132031 sD012
lem-CXcb-box-at02132031 : _
lem-CXcb-box-at02132031 = D012.lem-CXcb-box-at02132031 sD012
lem-P-box-at02132130 : _
lem-P-box-at02132130 = D012.lem-P-box-at02132130 sD012
lem-VPQ-at02132130 : _
lem-VPQ-at02132130 = D012.lem-VPQ-at02132130 sD012
lem-QVQ-at0213243041 : _
lem-QVQ-at0213243041 = D012.lem-QVQ-at0213243041 sD012
lem-P-box-at0310243241 : _
lem-P-box-at0310243241 = D012.lem-P-box-at0310243241 sD012
lem-CXbc-box-at03122130 : _
lem-CXbc-box-at03122130 = D012.lem-CXbc-box-at03122130 sD012
lem-CXcb-box-at03122130 : _
lem-CXcb-box-at03122130 = D012.lem-CXcb-box-at03122130 sD012
lem-VPQ-at03122031 : _
lem-VPQ-at03122031 = D012.lem-VPQ-at03122031 sD012
lem-CXbc-box-at03122031 : _
lem-CXbc-box-at03122031 = D012.lem-CXbc-box-at03122031 sD012
lem-CXcb-box-at03122031 : _
lem-CXcb-box-at03122031 = D012.lem-CXcb-box-at03122031 sD012
lem-P-box-at03122130 : _
lem-P-box-at03122130 = D012.lem-P-box-at03122130 sD012
lem-VPQ-at03122130 : _
lem-VPQ-at03122130 = D012.lem-VPQ-at03122130 sD012
lem-VPQ-at02142041 : _
lem-VPQ-at02142041 = D012.lem-VPQ-at02142041 sD012
lem-t-cP-at02142041 : _
lem-t-cP-at02142041 = D012.lem-t-cP-at02142041 sD012
lem-VPQ-at0314203241 : _
lem-VPQ-at0314203241 = D012.lem-VPQ-at0314203241 sD012
lem-t-cP-at0314203241 : _
lem-t-cP-at0314203241 = D012.lem-t-cP-at0314203241 sD012
lem-SWbc-box-at021021 : _
lem-SWbc-box-at021021 = D012.lem-SWbc-box-at021021 sD012
lem-VPQ-at02102331 : _
lem-VPQ-at02102331 = D012.lem-VPQ-at02102331 sD012
lem-P-box-at031031 : _
lem-P-box-at031031 = D012.lem-P-box-at031031 sD012
lem-CXbc-box-at142142 : _
lem-CXbc-box-at142142 = D012.lem-CXbc-box-at142142 sD012
lem-CXcb-box-at142142 : _
lem-CXcb-box-at142142 = D012.lem-CXcb-box-at142142 sD012
lem-P-box-at03243042 : _
lem-P-box-at03243042 = D012.lem-P-box-at03243042 sD012
lem-VPQ-at03243042 : _
lem-VPQ-at03243042 = D012.lem-VPQ-at03243042 sD012
lem-P-box-at2442 : _
lem-P-box-at2442 = D012.lem-P-box-at2442 sD012
lem-CXbc-box-at02102331 : _
lem-CXbc-box-at02102331 = D012.lem-CXbc-box-at02102331 sD012
lem-CXcb-box-at02102331 : _
lem-CXcb-box-at02102331 = D012.lem-CXcb-box-at02102331 sD012
lem-VPQ-at142142 : _
lem-VPQ-at142142 = D012.lem-VPQ-at142142 sD012
lem-t-cP-at142142 : _
lem-t-cP-at142142 = D012.lem-t-cP-at142142 sD012
lem-t-cP-at033440 : _
lem-t-cP-at033440 = D012.lem-t-cP-at033440 sD012
lem-t-cP-at0214203143 : _
lem-t-cP-at0214203143 = D012.lem-t-cP-at0214203143 sD012
lem-CXbc-box-at04122041 : _
lem-CXbc-box-at04122041 = D012.lem-CXbc-box-at04122041 sD012
lem-CXcb-box-at04122041 : _
lem-CXcb-box-at04122041 = D012.lem-CXcb-box-at04122041 sD012
lem-VPQ-at0412233041 : _
lem-VPQ-at0412233041 = D012.lem-VPQ-at0412233041 sD012
lem-VPQ-at04122041 : _
lem-VPQ-at04122041 = D012.lem-VPQ-at04122041 sD012
lem-SWbc-box-at0410213243 : _
lem-SWbc-box-at0410213243 = D012.lem-SWbc-box-at0410213243 sD012
lem-P-box-at04103143 : _
lem-P-box-at04103143 = D012.lem-P-box-at04103143 sD012
lem-VPQ-at04103143 : _
lem-VPQ-at04103143 = D012.lem-VPQ-at04103143 sD012
lem-VPQ-at04233042 : _
lem-VPQ-at04233042 = D012.lem-VPQ-at04233042 sD012
lem-CXbc-box-at0412233041 : _
lem-CXbc-box-at0412233041 = D012.lem-CXbc-box-at0412233041 sD012
lem-CXcb-box-at0412233041 : _
lem-CXcb-box-at0412233041 = D012.lem-CXcb-box-at0412233041 sD012
lem-P-box-at0412233041 : _
lem-P-box-at0412233041 = D012.lem-P-box-at0412233041 sD012
lem-CXbc-box-at041041 : _
lem-CXbc-box-at041041 = D012.lem-CXbc-box-at041041 sD012
lem-CXcb-box-at041041 : _
lem-CXcb-box-at041041 = D012.lem-CXcb-box-at041041 sD012
lem-P-box-at0410233241 : _
lem-P-box-at0410233241 = D012.lem-P-box-at0410233241 sD012
lem-VPQ-at0410233241 : _
lem-VPQ-at0410233241 = D012.lem-VPQ-at0410233241 sD012
lem-VPQ-at0412213043 : _
lem-VPQ-at0412213043 = D012.lem-VPQ-at0412213043 sD012
lem-P-box-at04122041 : _
lem-P-box-at04122041 = D012.lem-P-box-at04122041 sD012
lem-CXbc-box-at04233240 : _
lem-CXbc-box-at04233240 = D012.lem-CXbc-box-at04233240 sD012
lem-CXcb-box-at04233240 : _
lem-CXcb-box-at04233240 = D012.lem-CXcb-box-at04233240 sD012
lem-P-box-at0440 : _
lem-P-box-at0440 = D012.lem-P-box-at0440 sD012
lem-VPQ-at0440 : _
lem-VPQ-at0440 = D012.lem-VPQ-at0440 sD012
lem-CXbc-box-at0413203142 : _
lem-CXbc-box-at0413203142 = D012.lem-CXbc-box-at0413203142 sD012
lem-CXcb-box-at0413203142 : _
lem-CXcb-box-at0413203142 = D012.lem-CXcb-box-at0413203142 sD012
lem-VPQ-at02142140 : _
lem-VPQ-at02142140 = D012.lem-VPQ-at02142140 sD012
lem-CXbc-box-at0413213042 : _
lem-CXbc-box-at0413213042 = D012.lem-CXbc-box-at0413213042 sD012
lem-CXcb-box-at0413213042 : _
lem-CXcb-box-at0413213042 = D012.lem-CXcb-box-at0413213042 sD012
lem-P-box-at0413203142 : _
lem-P-box-at0413203142 = D012.lem-P-box-at0413203142 sD012
lem-VPQ-at0413203142 : _
lem-VPQ-at0413203142 = D012.lem-VPQ-at0413203142 sD012
lem-CXbc-box-at0440 : _
lem-CXbc-box-at0440 = D012.lem-CXbc-box-at0440 sD012
lem-CXcb-box-at0440 : _
lem-CXcb-box-at0440 = D012.lem-CXcb-box-at0440 sD012
sD014 : SD014
sD014 = lem-nat-SWbc-at0213243140 ∷ᵃ lem-nat-SWbc-at03102132 ∷ᵃ lem-nat-SWbc-at032032 ∷ᵃ lem-nat-SWbc-at04203243 ∷ᵃ lem-nat-SWbc-at13243142 ∷ᵃ lem-nat-SWbc-at13243241 ∷ᵃ lem-nat-SWbc-at14233142 ∷ᵃ lem-tP-at021021 ∷ᵃ lem-tP-at0210213443 ∷ᵃ lem-tP-at0213243140 ∷ᵃ lem-tP-at0220 ∷ᵃ lem-tP-at03102132 ∷ᵃ lem-tP-at032032 ∷ᵃ lem-tP-at0410213243 ∷ᵃ lem-tP-at04203243 ∷ᵃ lem-tP-at13243142 ∷ᵃ lem-tP-at13243241 ∷ᵃ lem-tP-at14233142 ∷ᵃ lem-tP-at14233241 ∷ᵃ lem-nat-SWbc-at0310213442 ∷ᵃ lem-nat-SWbc-at14233241 ∷ᵃ lem-nat-SWbc-at0220 ∷ᵃ lem-CSdu-box-1 ∷ᵃ lem-CSdu-box-2 ∷ᵃ lem-CSdu-box-2-at0210243143 ∷ᵃ lem-CSdu-box-2-at122441 ∷ᵃ lem-CSdu-box-2-at243243 ∷ᵃ lem-CSu-box-1 ∷ᵃ lem-CSu-box-2 ∷ᵃ lem-CSu-box-2-at122441 ∷ᵃ lem-CSu-box-2-at243243 ∷ᵃ lem-CXbc-box ∷ᵃ lem-CXbc-box-at0214203143 ∷ᵃ lem-CXbc-box-at0330 ∷ᵃ lem-CXbc-box-at043043 ∷ᵃ lem-CXbc-box-at1221 ∷ᵃ lem-CXbc-box-at12243143 ∷ᵃ lem-CXbc-box-at13213442 ∷ᵃ lem-CXbc-box-at133441 ∷ᵃ lem-CXcb-box ∷ᵃ lem-CXcb-box-at0214203143 ∷ᵃ lem-CXcb-box-at0330 ∷ᵃ lem-CXcb-box-at043043 ∷ᵃ lem-CXcb-box-at1221 ∷ᵃ lem-CXcb-box-at12243143 ∷ᵃ lem-CXcb-box-at13213442 ∷ᵃ lem-CXcb-box-at133441 ∷ᵃ lem-QVQ-at021021 ∷ᵃ lem-QVQ-at03102132 ∷ᵃ lem-QVQ-at0410213243 ∷ᵃ lem-QVQ-at04203243 ∷ᵃ lem-QVQ-at13243142 ∷ᵃ lem-QVQ-at13243241 ∷ᵃ lem-QVQ-at14233142 ∷ᵃ lem-SWbc-box-at032032 ∷ᵃ lem-SWbc-box-at04203243 ∷ᵃ lem-SWbc-box-at13243142 ∷ᵃ lem-SWbc-box-at13243241 ∷ᵃ lem-SWbc-box-at14233142 ∷ᵃ lem-Sdu-box ∷ᵃ lem-Su-box ∷ᵃ lem-Su-box-at0210243143 ∷ᵃ lem-Su-box-at122441 ∷ᵃ lem-Su-box-at243243 ∷ᵃ lem-VPQ ∷ᵃ lem-VPQ-at0110 ∷ᵃ lem-VPQ-at0210243143 ∷ᵃ lem-VPQ-at0310243142 ∷ᵃ lem-VPQ-at0314203142 ∷ᵃ lem-VPQ-at0330 ∷ᵃ lem-VPQ-at043043 ∷ᵃ lem-VPQ-at1221 ∷ᵃ lem-VPQ-at122331 ∷ᵃ lem-VPQ-at122441 ∷ᵃ lem-VPQ-at132132 ∷ᵃ lem-VPQ-at13213442 ∷ᵃ lem-VPQ-at1331 ∷ᵃ lem-VPQ-at2332 ∷ᵃ lem-VPQ-at243243 ∷ᵃ lem-VPQ-at3443 ∷ᵃ lem-CSu-box-2-at0210243143 ∷ᵃ lem-CXbc-box-at0210243143 ∷ᵃ lem-CXbc-box-at0213213440 ∷ᵃ lem-CXbc-box-at0214213043 ∷ᵃ lem-CXbc-box-at022330 ∷ᵃ lem-CXbc-box-at02233440 ∷ᵃ lem-CXbc-box-at022440 ∷ᵃ lem-CXbc-box-at0312213440 ∷ᵃ lem-CXbc-box-at0312243140 ∷ᵃ lem-CXbc-box-at0314203142 ∷ᵃ lem-CXbc-box-at0314213042 ∷ᵃ lem-CXbc-box-at122331 ∷ᵃ lem-CXbc-box-at12233441 ∷ᵃ lem-CXbc-box-at122441 ∷ᵃ lem-CXbc-box-at132132 ∷ᵃ lem-CXbc-box-at1331 ∷ᵃ lem-CXbc-box-at14213243 ∷ᵃ lem-CXbc-box-at1441 ∷ᵃ lem-CXbc-box-at2332 ∷ᵃ lem-CXbc-box-at243243 ∷ᵃ lem-CXcb-box-at0210243143 ∷ᵃ lem-CXcb-box-at0213213440 ∷ᵃ lem-CXcb-box-at0214213043 ∷ᵃ lem-CXcb-box-at022330 ∷ᵃ lem-CXcb-box-at02233440 ∷ᵃ lem-CXcb-box-at0312213440 ∷ᵃ lem-CXcb-box-at0312243140 ∷ᵃ lem-CXcb-box-at0314203142 ∷ᵃ lem-CXcb-box-at0314213042 ∷ᵃ lem-CXcb-box-at122331 ∷ᵃ lem-CXcb-box-at12233441 ∷ᵃ lem-CXcb-box-at122441 ∷ᵃ lem-CXcb-box-at132132 ∷ᵃ lem-CXcb-box-at1331 ∷ᵃ lem-CXcb-box-at14213243 ∷ᵃ lem-CXcb-box-at1441 ∷ᵃ lem-CXcb-box-at2332 ∷ᵃ lem-CXcb-box-at243243 ∷ᵃ lem-QVQ-at0210213443 ∷ᵃ lem-QVQ-at0213243140 ∷ᵃ lem-QVQ-at0220 ∷ᵃ lem-QVQ-at032032 ∷ᵃ lem-QVQ-at14233241 ∷ᵃ lem-SWbc-box-at0213243140 ∷ᵃ lem-SWbc-box-at0220 ∷ᵃ lem-SWbc-box-at03102132 ∷ᵃ lem-VPQ-at0210233441 ∷ᵃ lem-VPQ-at0213203441 ∷ᵃ lem-VPQ-at0214203143 ∷ᵃ lem-VPQ-at0214213043 ∷ᵃ lem-VPQ-at022330 ∷ᵃ lem-VPQ-at022440 ∷ᵃ lem-VPQ-at0312243140 ∷ᵃ lem-VPQ-at0314213042 ∷ᵃ lem-VPQ-at12213443 ∷ᵃ lem-VPQ-at12233441 ∷ᵃ lem-VPQ-at14213243 ∷ᵃ lem-VPQ-at143143 ∷ᵃ lem-VPQ-at233442 ∷ᵃ lem-CXbc-box-at0210233441 ∷ᵃ lem-CXbc-box-at02102441 ∷ᵃ lem-CXbc-box-at02142041 ∷ᵃ lem-CXbc-box-at0310243142 ∷ᵃ lem-CXbc-box-at0310243241 ∷ᵃ lem-CXbc-box-at031031 ∷ᵃ lem-CXbc-box-at03103441 ∷ᵃ lem-CXbc-box-at0312203441 ∷ᵃ lem-CXbc-box-at0312243041 ∷ᵃ lem-CXbc-box-at0314213240 ∷ᵃ lem-CXbc-box-at03143041 ∷ᵃ lem-CXbc-box-at03143140 ∷ᵃ lem-CXbc-box-at03243240 ∷ᵃ lem-CXbc-box-at033440 ∷ᵃ lem-CXbc-box-at12213443 ∷ᵃ lem-CXbc-box-at143143 ∷ᵃ lem-CXbc-box-at233442 ∷ᵃ lem-CXbc-box-at2442 ∷ᵃ lem-CXbc-box-at3443 ∷ᵃ lem-CXcb-box-at0210233441 ∷ᵃ lem-CXcb-box-at02102441 ∷ᵃ lem-CXcb-box-at022440 ∷ᵃ lem-CXcb-box-at0310243142 ∷ᵃ lem-CXcb-box-at0310243241 ∷ᵃ lem-CXcb-box-at031031 ∷ᵃ lem-CXcb-box-at03103441 ∷ᵃ lem-CXcb-box-at0312203441 ∷ᵃ lem-CXcb-box-at0312243041 ∷ᵃ lem-CXcb-box-at0314213240 ∷ᵃ lem-CXcb-box-at03143041 ∷ᵃ lem-CXcb-box-at03143140 ∷ᵃ lem-CXcb-box-at03243240 ∷ᵃ lem-CXcb-box-at033440 ∷ᵃ lem-CXcb-box-at12213443 ∷ᵃ lem-CXcb-box-at143143 ∷ᵃ lem-CXcb-box-at233442 ∷ᵃ lem-CXcb-box-at2442 ∷ᵃ lem-CXcb-box-at3443 ∷ᵃ lem-SWbc-box-at0310213442 ∷ᵃ lem-SWbc-box-at14233241 ∷ᵃ lem-VPQ-at02102441 ∷ᵃ lem-VPQ-at02233440 ∷ᵃ lem-VPQ-at0310243241 ∷ᵃ lem-VPQ-at031031 ∷ᵃ lem-VPQ-at03103441 ∷ᵃ lem-VPQ-at0312203441 ∷ᵃ lem-VPQ-at0312243041 ∷ᵃ lem-VPQ-at0314213240 ∷ᵃ lem-VPQ-at03143140 ∷ᵃ lem-VPQ-at03243240 ∷ᵃ lem-VPQ-at033440 ∷ᵃ lem-VPQ-at12243143 ∷ᵃ lem-VPQ-at1441 ∷ᵃ lem-VPQ-at2442 ∷ᵃ lem-CXcb-box-at02142041 ∷ᵃ nil
lem-QVQ : _
lem-QVQ = D014.lem-QVQ sD014
lem-QVQ-at0210243143 : _
lem-QVQ-at0210243143 = D014.lem-QVQ-at0210243143 sD014
lem-QVQ-at243243 : _
lem-QVQ-at243243 = D014.lem-QVQ-at243243 sD014
lem-QVQ-at122441 : _
lem-QVQ-at122441 = D014.lem-QVQ-at122441 sD014
lem-SWbc-box : _
lem-SWbc-box = D014.lem-SWbc-box sD014
lem-SWbc-box-at1221 : _
lem-SWbc-box-at1221 = D014.lem-SWbc-box-at1221 sD014
lem-QVQ-at1221 : _
lem-QVQ-at1221 = D014.lem-QVQ-at1221 sD014
lem-QVQ-at2332 : _
lem-QVQ-at2332 = D014.lem-QVQ-at2332 sD014
lem-sym-bc-at13243142 : _
lem-sym-bc-at13243142 = D014.lem-sym-bc-at13243142 sD014
lem-QVQ-at122331 : _
lem-QVQ-at122331 = D014.lem-QVQ-at122331 sD014
lem-sym-bc-at13243241 : _
lem-sym-bc-at13243241 = D014.lem-sym-bc-at13243241 sD014
lem-QVQ-at132132 : _
lem-QVQ-at132132 = D014.lem-QVQ-at132132 sD014
lem-SWbc-box-at12243143 : _
lem-SWbc-box-at12243143 = D014.lem-SWbc-box-at12243143 sD014
lem-sym-bc-at14233142 : _
lem-sym-bc-at14233142 = D014.lem-sym-bc-at14233142 sD014
lem-box-cP-at14233142 : _
lem-box-cP-at14233142 = D014.lem-box-cP-at14233142 sD014
lem-QVQ-at13213442 : _
lem-QVQ-at13213442 = D014.lem-QVQ-at13213442 sD014
lem-QVQ-at1331 : _
lem-QVQ-at1331 = D014.lem-QVQ-at1331 sD014
lem-QVQ-at0110 : _
lem-QVQ-at0110 = D014.lem-QVQ-at0110 sD014
lem-SWbc-box-at133441 : _
lem-SWbc-box-at133441 = D014.lem-SWbc-box-at133441 sD014
lem-box-cP-at13243241 : _
lem-box-cP-at13243241 = D014.lem-box-cP-at13243241 sD014
lem-box-cP-at021021 : _
lem-box-cP-at021021 = D014.lem-box-cP-at021021 sD014
lem-SWbc-box-at13213442 : _
lem-SWbc-box-at13213442 = D014.lem-SWbc-box-at13213442 sD014
lem-box-cP-at13243142 : _
lem-box-cP-at13243142 = D014.lem-box-cP-at13243142 sD014
lem-box-cP-at03102132 : _
lem-box-cP-at03102132 = D014.lem-box-cP-at03102132 sD014
lem-QVQ-at3443 : _
lem-QVQ-at3443 = D014.lem-QVQ-at3443 sD014
lem-box-cP-at0410213243 : _
lem-box-cP-at0410213243 = D014.lem-box-cP-at0410213243 sD014
lem-QVQ-at043043 : _
lem-QVQ-at043043 = D014.lem-QVQ-at043043 sD014
lem-SWbc-box-at043043 : _
lem-SWbc-box-at043043 = D014.lem-SWbc-box-at043043 sD014
lem-box-cP-at04203243 : _
lem-box-cP-at04203243 = D014.lem-box-cP-at04203243 sD014
lem-QVQ-at0330 : _
lem-QVQ-at0330 = D014.lem-QVQ-at0330 sD014
lem-QVQ-at0314203142 : _
lem-QVQ-at0314203142 = D014.lem-QVQ-at0314203142 sD014
lem-QVQ-at0310243142 : _
lem-QVQ-at0310243142 = D014.lem-QVQ-at0310243142 sD014
lem-sym-bc-at04203243 : _
lem-sym-bc-at04203243 = D014.lem-sym-bc-at04203243 sD014
lem-sym-bc-at032032 : _
lem-sym-bc-at032032 = D014.lem-sym-bc-at032032 sD014
lem-SWbc-box-at0330 : _
lem-SWbc-box-at0330 = D014.lem-SWbc-box-at0330 sD014
lem-XCSX-box-2-at243243 : _
lem-XCSX-box-2-at243243 = D014.lem-XCSX-box-2-at243243 sD014
lem-XCSX-box-2-at122441 : _
lem-XCSX-box-2-at122441 = D014.lem-XCSX-box-2-at122441 sD014
lem-XCSX-box-2-at0210243143 : _
lem-XCSX-box-2-at0210243143 = D014.lem-XCSX-box-2-at0210243143 sD014
lem-SWbc-box-at0214203143 : _
lem-SWbc-box-at0214203143 = D014.lem-SWbc-box-at0214203143 sD014
lem-QVQ-at0214213043 : _
lem-QVQ-at0214213043 = D014.lem-QVQ-at0214213043 sD014
lem-QVQ-at0210233441 : _
lem-QVQ-at0210233441 = D014.lem-QVQ-at0210233441 sD014
lem-SWbc-box-at122441 : _
lem-SWbc-box-at122441 = D014.lem-SWbc-box-at122441 sD014
lem-QVQ-at12233441 : _
lem-QVQ-at12233441 = D014.lem-QVQ-at12233441 sD014
lem-SWbc-box-at14213243 : _
lem-SWbc-box-at14213243 = D014.lem-SWbc-box-at14213243 sD014
lem-QVQ-at143143 : _
lem-QVQ-at143143 = D014.lem-QVQ-at143143 sD014
lem-QVQ-at233442 : _
lem-QVQ-at233442 = D014.lem-QVQ-at233442 sD014
lem-SWbc-box-at0210243143 : _
lem-SWbc-box-at0210243143 = D014.lem-SWbc-box-at0210243143 sD014
lem-box-cP-at0210213443 : _
lem-box-cP-at0210213443 = D014.lem-box-cP-at0210213443 sD014
lem-SWbc-box-at243243 : _
lem-SWbc-box-at243243 = D014.lem-SWbc-box-at243243 sD014
lem-SWbc-box-at1441 : _
lem-SWbc-box-at1441 = D014.lem-SWbc-box-at1441 sD014
lem-box-cP-at14233241 : _
lem-box-cP-at14233241 = D014.lem-box-cP-at14233241 sD014
lem-QVQ-at12213443 : _
lem-QVQ-at12213443 = D014.lem-QVQ-at12213443 sD014
lem-F4-CS0-S2 : _
lem-F4-CS0-S2 = D014.lem-F4-CS0-S2 sD014
lem-F4-CS1-S0 : _
lem-F4-CS1-S0 = D014.lem-F4-CS1-S0 sD014
lem-F4-CS2-S0 : _
lem-F4-CS2-S0 = D014.lem-F4-CS2-S0 sD014
lem-SWbc-box-at0314213042 : _
lem-SWbc-box-at0314213042 = D014.lem-SWbc-box-at0314213042 sD014
lem-QVQ-at0213203441 : _
lem-QVQ-at0213203441 = D014.lem-QVQ-at0213203441 sD014
lem-SWbc-box-at0314203142 : _
lem-SWbc-box-at0314203142 = D014.lem-SWbc-box-at0314203142 sD014
lem-QVQ-at0314213042 : _
lem-QVQ-at0314213042 = D014.lem-QVQ-at0314213042 sD014
lem-SWbc-box-at0214213043 : _
lem-SWbc-box-at0214213043 = D014.lem-SWbc-box-at0214213043 sD014
lem-SWbc-box-at1331 : _
lem-SWbc-box-at1331 = D014.lem-SWbc-box-at1331 sD014
lem-box-cP-at032032 : _
lem-box-cP-at032032 = D014.lem-box-cP-at032032 sD014
lem-SWbc-box-at0312243140 : _
lem-SWbc-box-at0312243140 = D014.lem-SWbc-box-at0312243140 sD014
lem-SWbc-box-at0312213440 : _
lem-SWbc-box-at0312213440 = D014.lem-SWbc-box-at0312213440 sD014
lem-QVQ-at0312243140 : _
lem-QVQ-at0312243140 = D014.lem-QVQ-at0312243140 sD014
lem-SWbc-box-at132132 : _
lem-SWbc-box-at132132 = D014.lem-SWbc-box-at132132 sD014
lem-SWbc-box-at022330 : _
lem-SWbc-box-at022330 = D014.lem-SWbc-box-at022330 sD014
lem-box-cP-at0220 : _
lem-box-cP-at0220 = D014.lem-box-cP-at0220 sD014
lem-sym-bc-at0213243140 : _
lem-sym-bc-at0213243140 = D014.lem-sym-bc-at0213243140 sD014
lem-SWbc-box-at0213213440 : _
lem-SWbc-box-at0213213440 = D014.lem-SWbc-box-at0213213440 sD014
lem-box-cP-at0213243140 : _
lem-box-cP-at0213243140 = D014.lem-box-cP-at0213243140 sD014
lem-sym-bc-at0220 : _
lem-sym-bc-at0220 = D014.lem-sym-bc-at0220 sD014
lem-QVQ-at022330 : _
lem-QVQ-at022330 = D014.lem-QVQ-at022330 sD014
lem-SWbc-box-at122331 : _
lem-SWbc-box-at122331 = D014.lem-SWbc-box-at122331 sD014
lem-QVQ-at14213243 : _
lem-QVQ-at14213243 = D014.lem-QVQ-at14213243 sD014
lem-SWbc-box-at12233441 : _
lem-SWbc-box-at12233441 = D014.lem-SWbc-box-at12233441 sD014
lem-SWbc-box-at2332 : _
lem-SWbc-box-at2332 = D014.lem-SWbc-box-at2332 sD014
lem-F2-S0-CS1 : _
lem-F2-S0-CS1 = D014.lem-F2-S0-CS1 sD014
lem-F2-S0-CS2 : _
lem-F2-S0-CS2 = D014.lem-F2-S0-CS2 sD014
lem-F2-S2-CS0 : _
lem-F2-S2-CS0 = D014.lem-F2-S2-CS0 sD014
lem-sym-bc-at03102132 : _
lem-sym-bc-at03102132 = D014.lem-sym-bc-at03102132 sD014
lem-QVQ-at0214203143 : _
lem-QVQ-at0214203143 = D014.lem-QVQ-at0214203143 sD014
lem-SWbc-box-at02233440 : _
lem-SWbc-box-at02233440 = D014.lem-SWbc-box-at02233440 sD014
lem-QVQ-at022440 : _
lem-QVQ-at022440 = D014.lem-QVQ-at022440 sD014
lem-SWbc-box-at022440 : _
lem-SWbc-box-at022440 = D014.lem-SWbc-box-at022440 sD014
lem-QVQ-at02233440 : _
lem-QVQ-at02233440 = D014.lem-QVQ-at02233440 sD014
lem-QVQ-at1441 : _
lem-QVQ-at1441 = D014.lem-QVQ-at1441 sD014
lem-SWbc-box-at0210233441 : _
lem-SWbc-box-at0210233441 = D014.lem-SWbc-box-at0210233441 sD014
lem-QVQ-at02102441 : _
lem-QVQ-at02102441 = D014.lem-QVQ-at02102441 sD014
lem-SWbc-box-at02102441 : _
lem-SWbc-box-at02102441 = D014.lem-SWbc-box-at02102441 sD014
lem-SWbc-box-at233442 : _
lem-SWbc-box-at233442 = D014.lem-SWbc-box-at233442 sD014
lem-QVQ-at2442 : _
lem-QVQ-at2442 = D014.lem-QVQ-at2442 sD014
lem-SWbc-box-at2442 : _
lem-SWbc-box-at2442 = D014.lem-SWbc-box-at2442 sD014
lem-SWbc-box-at143143 : _
lem-SWbc-box-at143143 = D014.lem-SWbc-box-at143143 sD014
lem-SWbc-box-at12213443 : _
lem-SWbc-box-at12213443 = D014.lem-SWbc-box-at12213443 sD014
lem-QVQ-at12243143 : _
lem-QVQ-at12243143 = D014.lem-QVQ-at12243143 sD014
lem-sym-bc-at14233241 : _
lem-sym-bc-at14233241 = D014.lem-sym-bc-at14233241 sD014
lem-SWbc-box-at03143140 : _
lem-SWbc-box-at03143140 = D014.lem-SWbc-box-at03143140 sD014
lem-QVQ-at0314213240 : _
lem-QVQ-at0314213240 = D014.lem-QVQ-at0314213240 sD014
lem-SWbc-box-at0314213240 : _
lem-SWbc-box-at0314213240 = D014.lem-SWbc-box-at0314213240 sD014
lem-QVQ-at03143140 : _
lem-QVQ-at03143140 = D014.lem-QVQ-at03143140 sD014
lem-QVQ-at03243240 : _
lem-QVQ-at03243240 = D014.lem-QVQ-at03243240 sD014
lem-SWbc-box-at033440 : _
lem-SWbc-box-at033440 = D014.lem-SWbc-box-at033440 sD014
lem-SWbc-box-at03243240 : _
lem-SWbc-box-at03243240 = D014.lem-SWbc-box-at03243240 sD014
lem-QVQ-at033440 : _
lem-QVQ-at033440 = D014.lem-QVQ-at033440 sD014
lem-SWbc-box-at03103441 : _
lem-SWbc-box-at03103441 = D014.lem-SWbc-box-at03103441 sD014
lem-QVQ-at0310243241 : _
lem-QVQ-at0310243241 = D014.lem-QVQ-at0310243241 sD014
lem-SWbc-box-at0310243241 : _
lem-SWbc-box-at0310243241 = D014.lem-SWbc-box-at0310243241 sD014
lem-QVQ-at03103441 : _
lem-QVQ-at03103441 = D014.lem-QVQ-at03103441 sD014
lem-SWbc-box-at0310243142 : _
lem-SWbc-box-at0310243142 = D014.lem-SWbc-box-at0310243142 sD014
lem-sym-bc-at0310213442 : _
lem-sym-bc-at0310213442 = D014.lem-sym-bc-at0310213442 sD014
lem-SWbc-box-at0312203441 : _
lem-SWbc-box-at0312203441 = D014.lem-SWbc-box-at0312203441 sD014
lem-QVQ-at0312243041 : _
lem-QVQ-at0312243041 = D014.lem-QVQ-at0312243041 sD014
lem-SWbc-box-at0312243041 : _
lem-SWbc-box-at0312243041 = D014.lem-SWbc-box-at0312243041 sD014
lem-QVQ-at0312203441 : _
lem-QVQ-at0312203441 = D014.lem-QVQ-at0312203441 sD014
lem-SWbc-box-at3443 : _
lem-SWbc-box-at3443 = D014.lem-SWbc-box-at3443 sD014
lem-SWbc-box-at031031 : _
lem-SWbc-box-at031031 = D014.lem-SWbc-box-at031031 sD014
lem-QVQ-at031031 : _
lem-QVQ-at031031 = D014.lem-QVQ-at031031 sD014
lem-SWbc-box-at03143041 : _
lem-SWbc-box-at03143041 = D014.lem-SWbc-box-at03143041 sD014
lem-SWbc-box-at02142041 : _
lem-SWbc-box-at02142041 = D014.lem-SWbc-box-at02142041 sD014
sD013 : SD013
sD013 = lem-box-tQ-at0214203143 ∷ᵃ lem-box-tQ-at043043 ∷ᵃ lem-tP-at043043 ∷ᵃ lem-box-tQ-at02132031 ∷ᵃ lem-box-tQ-at022440 ∷ᵃ lem-box-tQ-at03122031 ∷ᵃ lem-box-tQ-at04122041 ∷ᵃ lem-tP-at02132031 ∷ᵃ lem-tP-at022440 ∷ᵃ lem-tP-at03122031 ∷ᵃ lem-tP-at04122041 ∷ᵃ lem-CSdu-box-2-at04203243 ∷ᵃ lem-Su-box-at04203243 ∷ᵃ lem-box-tQ-at0410233142 ∷ᵃ lem-box-tQ-at04122140 ∷ᵃ lem-box-tQ-at0412233140 ∷ᵃ lem-box-tQ-at0413203241 ∷ᵃ lem-box-tQ-at0413213240 ∷ᵃ lem-box-tQ-at04133140 ∷ᵃ lem-tP-at0410233142 ∷ᵃ lem-tP-at04122140 ∷ᵃ lem-tP-at0412233140 ∷ᵃ lem-tP-at0413203241 ∷ᵃ lem-tP-at0413213240 ∷ᵃ lem-tP-at0440 ∷ᵃ nil
lem-P-box-at0413213240 : _
lem-P-box-at0413213240 = D013.lem-P-box-at0413213240 sD013
lem-VPQ-at0413213240 : _
lem-VPQ-at0413213240 = D013.lem-VPQ-at0413213240 sD013
lem-CXbc-box-at0412233140 : _
lem-CXbc-box-at0412233140 = D013.lem-CXbc-box-at0412233140 sD013
lem-CXcb-box-at0412233140 : _
lem-CXcb-box-at0412233140 = D013.lem-CXcb-box-at0412233140 sD013
lem-VPQ-at0410233142 : _
lem-VPQ-at0410233142 = D013.lem-VPQ-at0410233142 sD013
lem-CXbc-box-at04122140 : _
lem-CXbc-box-at04122140 = D013.lem-CXbc-box-at04122140 sD013
lem-CXcb-box-at04122140 : _
lem-CXcb-box-at04122140 = D013.lem-CXcb-box-at04122140 sD013
lem-VPQ-at0412233140 : _
lem-VPQ-at0412233140 = D013.lem-VPQ-at0412233140 sD013
lem-CSdu-box-2-at04122041 : _
lem-CSdu-box-2-at04122041 = D013.lem-CSdu-box-2-at04122041 sD013
lem-Su-box-at04122041 : _
lem-Su-box-at04122041 = D013.lem-Su-box-at04122041 sD013
lem-VPQ-at0413203241 : _
lem-VPQ-at0413203241 = D013.lem-VPQ-at0413203241 sD013
lem-VPQ-at04122140 : _
lem-VPQ-at04122140 = D013.lem-VPQ-at04122140 sD013
lem-XCSX-box-2-at04203243 : _
lem-XCSX-box-2-at04203243 = D013.lem-XCSX-box-2-at04203243 sD013
lem-CXbc-box-at04133140 : _
lem-CXbc-box-at04133140 = D013.lem-CXbc-box-at04133140 sD013
lem-CXcb-box-at04133140 : _
lem-CXcb-box-at04133140 = D013.lem-CXcb-box-at04133140 sD013
lem-CXbc-box-at0413213240 : _
lem-CXbc-box-at0413213240 = D013.lem-CXbc-box-at0413213240 sD013
lem-CXcb-box-at0413213240 : _
lem-CXcb-box-at0413213240 = D013.lem-CXcb-box-at0413213240 sD013
sD015 : SD015
sD015 = lem-nat-SWbc-at021021 ∷ᵃ lem-nat-SWbc-at0210213443 ∷ᵃ lem-nat-SWbc-at0410213243 ∷ᵃ lem-tP-at0213243041 ∷ᵃ lem-tP-at0214233041 ∷ᵃ lem-tP-at0310213442 ∷ᵃ lem-nat-SWbc-at0214233041 ∷ᵃ lem-CXbc-box-at02102331 ∷ᵃ lem-CXbc-box-at02132031 ∷ᵃ lem-CXbc-box-at02132130 ∷ᵃ lem-CXbc-box-at03122031 ∷ᵃ lem-CXbc-box-at03122130 ∷ᵃ lem-CXbc-box-at0314203241 ∷ᵃ lem-CXbc-box-at041041 ∷ᵃ lem-CXbc-box-at04122041 ∷ᵃ lem-CXbc-box-at0412233041 ∷ᵃ lem-CXbc-box-at0413203142 ∷ᵃ lem-CXbc-box-at0413213042 ∷ᵃ lem-CXbc-box-at04233240 ∷ᵃ lem-CXbc-box-at0440 ∷ᵃ lem-CXbc-box-at142142 ∷ᵃ lem-CXcb-box-at02102331 ∷ᵃ lem-CXcb-box-at02132031 ∷ᵃ lem-CXcb-box-at02132130 ∷ᵃ lem-CXcb-box-at03122031 ∷ᵃ lem-CXcb-box-at03122130 ∷ᵃ lem-CXcb-box-at0314203241 ∷ᵃ lem-CXcb-box-at041041 ∷ᵃ lem-CXcb-box-at04122041 ∷ᵃ lem-CXcb-box-at0412233041 ∷ᵃ lem-CXcb-box-at0413203142 ∷ᵃ lem-CXcb-box-at0413213042 ∷ᵃ lem-CXcb-box-at04233240 ∷ᵃ lem-CXcb-box-at0440 ∷ᵃ lem-CXcb-box-at142142 ∷ᵃ lem-QVQ-at0213243041 ∷ᵃ lem-QVQ-at0214233041 ∷ᵃ lem-QVQ-at0310213442 ∷ᵃ lem-SWbc-box-at021021 ∷ᵃ lem-SWbc-box-at0210213443 ∷ᵃ lem-SWbc-box-at0214233041 ∷ᵃ lem-SWbc-box-at0410213243 ∷ᵃ lem-VPQ-at02102331 ∷ᵃ lem-VPQ-at02132031 ∷ᵃ lem-VPQ-at02132130 ∷ᵃ lem-VPQ-at02142041 ∷ᵃ lem-VPQ-at02142140 ∷ᵃ lem-VPQ-at03122031 ∷ᵃ lem-VPQ-at03122130 ∷ᵃ lem-VPQ-at0314203241 ∷ᵃ lem-VPQ-at03143041 ∷ᵃ lem-VPQ-at03243042 ∷ᵃ lem-VPQ-at0410233241 ∷ᵃ lem-VPQ-at04103143 ∷ᵃ lem-VPQ-at04122041 ∷ᵃ lem-VPQ-at0412213043 ∷ᵃ lem-VPQ-at0412233041 ∷ᵃ lem-VPQ-at0413203142 ∷ᵃ lem-VPQ-at04233042 ∷ᵃ lem-VPQ-at0440 ∷ᵃ lem-VPQ-at142142 ∷ᵃ lem-CSdu-box-2-at04122041 ∷ᵃ lem-CXbc-box-at04122140 ∷ᵃ lem-CXbc-box-at0412233140 ∷ᵃ lem-CXbc-box-at0413213240 ∷ᵃ lem-CXbc-box-at04133140 ∷ᵃ lem-CXcb-box-at04122140 ∷ᵃ lem-CXcb-box-at0412233140 ∷ᵃ lem-CXcb-box-at0413213240 ∷ᵃ lem-CXcb-box-at04133140 ∷ᵃ lem-Su-box-at04122041 ∷ᵃ lem-VPQ-at0410233142 ∷ᵃ lem-VPQ-at04122140 ∷ᵃ lem-VPQ-at0412233140 ∷ᵃ lem-VPQ-at0413203241 ∷ᵃ lem-VPQ-at0413213240 ∷ᵃ lem-XCSX-box-2-at04203243 ∷ᵃ nil
lem-box-cP-at0214233041 : _
lem-box-cP-at0214233041 = D015.lem-box-cP-at0214233041 sD015
lem-SWbc-box-at0314203241 : _
lem-SWbc-box-at0314203241 = D015.lem-SWbc-box-at0314203241 sD015
lem-sym-bc-at0210213443 : _
lem-sym-bc-at0210213443 = D015.lem-sym-bc-at0210213443 sD015
lem-sym-bc-at0214233041 : _
lem-sym-bc-at0214233041 = D015.lem-sym-bc-at0214233041 sD015
lem-SWbc-box-at02132130 : _
lem-SWbc-box-at02132130 = D015.lem-SWbc-box-at02132130 sD015
lem-QVQ-at03143041 : _
lem-QVQ-at03143041 = D015.lem-QVQ-at03143041 sD015
lem-QVQ-at02132031 : _
lem-QVQ-at02132031 = D015.lem-QVQ-at02132031 sD015
lem-box-cP-at0310213442 : _
lem-box-cP-at0310213442 = D015.lem-box-cP-at0310213442 sD015
lem-SWbc-box-at02132031 : _
lem-SWbc-box-at02132031 = D015.lem-SWbc-box-at02132031 sD015
lem-QVQ-at02132130 : _
lem-QVQ-at02132130 = D015.lem-QVQ-at02132130 sD015
lem-box-cP-at0213243041 : _
lem-box-cP-at0213243041 = D015.lem-box-cP-at0213243041 sD015
lem-SWbc-box-at03122130 : _
lem-SWbc-box-at03122130 = D015.lem-SWbc-box-at03122130 sD015
lem-QVQ-at03122031 : _
lem-QVQ-at03122031 = D015.lem-QVQ-at03122031 sD015
lem-SWbc-box-at03122031 : _
lem-SWbc-box-at03122031 = D015.lem-SWbc-box-at03122031 sD015
lem-QVQ-at03122130 : _
lem-QVQ-at03122130 = D015.lem-QVQ-at03122130 sD015
lem-QVQ-at02142041 : _
lem-QVQ-at02142041 = D015.lem-QVQ-at02142041 sD015
lem-QVQ-at0314203241 : _
lem-QVQ-at0314203241 = D015.lem-QVQ-at0314203241 sD015
lem-sym-bc-at021021 : _
lem-sym-bc-at021021 = D015.lem-sym-bc-at021021 sD015
lem-QVQ-at02102331 : _
lem-QVQ-at02102331 = D015.lem-QVQ-at02102331 sD015
lem-SWbc-box-at142142 : _
lem-SWbc-box-at142142 = D015.lem-SWbc-box-at142142 sD015
lem-QVQ-at03243042 : _
lem-QVQ-at03243042 = D015.lem-QVQ-at03243042 sD015
lem-SWbc-box-at02102331 : _
lem-SWbc-box-at02102331 = D015.lem-SWbc-box-at02102331 sD015
lem-QVQ-at142142 : _
lem-QVQ-at142142 = D015.lem-QVQ-at142142 sD015
lem-SWbc-box-at04122041 : _
lem-SWbc-box-at04122041 = D015.lem-SWbc-box-at04122041 sD015
lem-QVQ-at0412233041 : _
lem-QVQ-at0412233041 = D015.lem-QVQ-at0412233041 sD015
lem-QVQ-at04122041 : _
lem-QVQ-at04122041 = D015.lem-QVQ-at04122041 sD015
lem-QVQ-at04103143 : _
lem-QVQ-at04103143 = D015.lem-QVQ-at04103143 sD015
lem-QVQ-at04233042 : _
lem-QVQ-at04233042 = D015.lem-QVQ-at04233042 sD015
lem-SWbc-box-at0412233041 : _
lem-SWbc-box-at0412233041 = D015.lem-SWbc-box-at0412233041 sD015
lem-SWbc-box-at041041 : _
lem-SWbc-box-at041041 = D015.lem-SWbc-box-at041041 sD015
lem-QVQ-at0410233241 : _
lem-QVQ-at0410233241 = D015.lem-QVQ-at0410233241 sD015
lem-QVQ-at0412213043 : _
lem-QVQ-at0412213043 = D015.lem-QVQ-at0412213043 sD015
lem-SWbc-box-at04233240 : _
lem-SWbc-box-at04233240 = D015.lem-SWbc-box-at04233240 sD015
lem-QVQ-at0440 : _
lem-QVQ-at0440 = D015.lem-QVQ-at0440 sD015
lem-SWbc-box-at0413203142 : _
lem-SWbc-box-at0413203142 = D015.lem-SWbc-box-at0413203142 sD015
lem-QVQ-at02142140 : _
lem-QVQ-at02142140 = D015.lem-QVQ-at02142140 sD015
lem-SWbc-box-at0413213042 : _
lem-SWbc-box-at0413213042 = D015.lem-SWbc-box-at0413213042 sD015
lem-QVQ-at0413203142 : _
lem-QVQ-at0413203142 = D015.lem-QVQ-at0413203142 sD015
lem-SWbc-box-at0440 : _
lem-SWbc-box-at0440 = D015.lem-SWbc-box-at0440 sD015
lem-QVQ-at0413213240 : _
lem-QVQ-at0413213240 = D015.lem-QVQ-at0413213240 sD015
lem-SWbc-box-at0412233140 : _
lem-SWbc-box-at0412233140 = D015.lem-SWbc-box-at0412233140 sD015
lem-QVQ-at0410233142 : _
lem-QVQ-at0410233142 = D015.lem-QVQ-at0410233142 sD015
lem-SWbc-box-at04122140 : _
lem-SWbc-box-at04122140 = D015.lem-SWbc-box-at04122140 sD015
lem-QVQ-at0412233140 : _
lem-QVQ-at0412233140 = D015.lem-QVQ-at0412233140 sD015
lem-XCSX-box-2-at04122041 : _
lem-XCSX-box-2-at04122041 = D015.lem-XCSX-box-2-at04122041 sD015
lem-QVQ-at0413203241 : _
lem-QVQ-at0413203241 = D015.lem-QVQ-at0413203241 sD015
lem-QVQ-at04122140 : _
lem-QVQ-at04122140 = D015.lem-QVQ-at04122140 sD015
lem-SWbc-box-at04133140 : _
lem-SWbc-box-at04133140 = D015.lem-SWbc-box-at04133140 sD015
lem-SWbc-box-at0413213240 : _
lem-SWbc-box-at0413213240 = D015.lem-SWbc-box-at0413213240 sD015
sD016 : SD016
sD016 = lem-nat-SWbc-at0214203143 ∷ᵃ lem-nat-SWbc-at0214213043 ∷ᵃ lem-nat-SWbc-at0314203142 ∷ᵃ lem-nat-SWbc-at0314213042 ∷ᵃ lem-nat-SWbc-at122441 ∷ᵃ lem-nat-SWbc-at132132 ∷ᵃ lem-nat-SWbc-at1331 ∷ᵃ lem-nat-SWbc-at14213243 ∷ᵃ lem-sym-ab-at03102132 ∷ᵃ lem-sym-ab-at0410213243 ∷ᵃ lem-nat-SWbc-at0210233441 ∷ᵃ lem-nat-SWbc-at02102441 ∷ᵃ lem-nat-SWbc-at02132031 ∷ᵃ lem-nat-SWbc-at02132130 ∷ᵃ lem-nat-SWbc-at02233440 ∷ᵃ lem-nat-SWbc-at022440 ∷ᵃ lem-nat-SWbc-at0310243241 ∷ᵃ lem-nat-SWbc-at03103441 ∷ᵃ lem-nat-SWbc-at03122031 ∷ᵃ lem-nat-SWbc-at03122130 ∷ᵃ lem-nat-SWbc-at03243240 ∷ᵃ lem-nat-SWbc-at033440 ∷ᵃ lem-nat-SWbc-at12233441 ∷ᵃ lem-nat-SWbc-at143143 ∷ᵃ lem-nat-SWbc-at233442 ∷ᵃ lem-nat-SWbc-at2442 ∷ᵃ lem-sym-ab-at0213243041 ∷ᵃ lem-box-tQ-at0210213443 ∷ᵃ lem-box-tQ-at0213243140 ∷ᵃ lem-box-tQ-at0220 ∷ᵃ lem-nat-SWbc ∷ᵃ lem-nat-SWbc-at0210243143 ∷ᵃ lem-nat-SWbc-at0213213440 ∷ᵃ lem-nat-SWbc-at0312213440 ∷ᵃ lem-nat-SWbc-at0312243140 ∷ᵃ lem-nat-SWbc-at0330 ∷ᵃ lem-nat-SWbc-at043043 ∷ᵃ lem-nat-SWbc-at1221 ∷ᵃ lem-nat-SWbc-at122331 ∷ᵃ lem-nat-SWbc-at12243143 ∷ᵃ lem-nat-SWbc-at13213442 ∷ᵃ lem-nat-SWbc-at133441 ∷ᵃ lem-nat-SWbc-at1441 ∷ᵃ lem-nat-SWbc-at2332 ∷ᵃ lem-nat-SWbc-at243243 ∷ᵃ lem-box-tQ-at021021 ∷ᵃ lem-box-tQ-at0213243041 ∷ᵃ lem-box-tQ-at0214233041 ∷ᵃ lem-nat-SWbc-at0310243142 ∷ᵃ lem-nat-SWbc-at031031 ∷ᵃ lem-nat-SWbc-at0312203441 ∷ᵃ lem-nat-SWbc-at0312243041 ∷ᵃ lem-nat-SWbc-at0314203241 ∷ᵃ lem-nat-SWbc-at0314213240 ∷ᵃ lem-nat-SWbc-at03143041 ∷ᵃ lem-nat-SWbc-at03143140 ∷ᵃ lem-nat-SWbc-at12213443 ∷ᵃ lem-nat-SWbc-at3443 ∷ᵃ lem-P-box-at0220 ∷ᵃ lem-P-box-at032032 ∷ᵃ lem-P-box-at13243142 ∷ᵃ lem-P-box-at13243241 ∷ᵃ lem-P-box-at14233142 ∷ᵃ lem-P-box-at14233241 ∷ᵃ lem-box-tQ ∷ᵃ lem-box-tQ-at0312243140 ∷ᵃ lem-box-tQ-at1221 ∷ᵃ lem-box-tQ-at12213443 ∷ᵃ lem-box-tQ-at3443 ∷ᵃ lem-nat-SWbc-at022330 ∷ᵃ lem-tP ∷ᵃ lem-tP-at0110 ∷ᵃ lem-tP-at0210233441 ∷ᵃ lem-tP-at0210243143 ∷ᵃ lem-tP-at0213203441 ∷ᵃ lem-tP-at0214213043 ∷ᵃ lem-tP-at0310243142 ∷ᵃ lem-tP-at0312243140 ∷ᵃ lem-tP-at0314203142 ∷ᵃ lem-tP-at0314213042 ∷ᵃ lem-tP-at0330 ∷ᵃ lem-tP-at043043 ∷ᵃ lem-tP-at1221 ∷ᵃ lem-tP-at12213443 ∷ᵃ lem-tP-at122331 ∷ᵃ lem-tP-at12233441 ∷ᵃ lem-tP-at122441 ∷ᵃ lem-tP-at132132 ∷ᵃ lem-tP-at13213442 ∷ᵃ lem-tP-at1331 ∷ᵃ lem-tP-at143143 ∷ᵃ lem-tP-at2332 ∷ᵃ lem-tP-at233442 ∷ᵃ lem-tP-at243243 ∷ᵃ lem-tP-at3443 ∷ᵃ lem-P-box-at021021 ∷ᵃ lem-P-box-at0210213443 ∷ᵃ lem-P-box-at0213243041 ∷ᵃ lem-P-box-at0213243140 ∷ᵃ lem-P-box-at0214233041 ∷ᵃ lem-P-box-at03102132 ∷ᵃ lem-P-box-at0310213442 ∷ᵃ lem-box-tQ-at0312243041 ∷ᵃ lem-box-tQ-at03143041 ∷ᵃ lem-nat-SWbc-at02142041 ∷ᵃ lem-tP-at02102441 ∷ᵃ lem-tP-at02132031 ∷ᵃ lem-tP-at02132130 ∷ᵃ lem-tP-at0214203143 ∷ᵃ lem-tP-at022330 ∷ᵃ lem-tP-at02233440 ∷ᵃ lem-tP-at022440 ∷ᵃ lem-tP-at0310243241 ∷ᵃ lem-tP-at031031 ∷ᵃ lem-tP-at03103441 ∷ᵃ lem-tP-at03122031 ∷ᵃ lem-tP-at0312203441 ∷ᵃ lem-tP-at03122130 ∷ᵃ lem-tP-at0312243041 ∷ᵃ lem-tP-at0314213240 ∷ᵃ lem-tP-at03143041 ∷ᵃ lem-tP-at03143140 ∷ᵃ lem-tP-at03243240 ∷ᵃ lem-tP-at033440 ∷ᵃ lem-tP-at12243143 ∷ᵃ lem-tP-at14213243 ∷ᵃ lem-tP-at1441 ∷ᵃ lem-tP-at2442 ∷ᵃ lem-QVQ ∷ᵃ lem-QVQ-at0110 ∷ᵃ lem-QVQ-at0210233441 ∷ᵃ lem-QVQ-at0210243143 ∷ᵃ lem-QVQ-at02102441 ∷ᵃ lem-QVQ-at0213203441 ∷ᵃ lem-QVQ-at0214203143 ∷ᵃ lem-QVQ-at0214213043 ∷ᵃ lem-QVQ-at022330 ∷ᵃ lem-QVQ-at02233440 ∷ᵃ lem-QVQ-at022440 ∷ᵃ lem-QVQ-at0310243142 ∷ᵃ lem-QVQ-at0310243241 ∷ᵃ lem-QVQ-at031031 ∷ᵃ lem-QVQ-at03103441 ∷ᵃ lem-QVQ-at0312203441 ∷ᵃ lem-QVQ-at0312243041 ∷ᵃ lem-QVQ-at0312243140 ∷ᵃ lem-QVQ-at0314203142 ∷ᵃ lem-QVQ-at0314213042 ∷ᵃ lem-QVQ-at0314213240 ∷ᵃ lem-QVQ-at03143140 ∷ᵃ lem-QVQ-at03243240 ∷ᵃ lem-QVQ-at0330 ∷ᵃ lem-QVQ-at033440 ∷ᵃ lem-QVQ-at043043 ∷ᵃ lem-QVQ-at1221 ∷ᵃ lem-QVQ-at12213443 ∷ᵃ lem-QVQ-at122331 ∷ᵃ lem-QVQ-at12233441 ∷ᵃ lem-QVQ-at12243143 ∷ᵃ lem-QVQ-at122441 ∷ᵃ lem-QVQ-at132132 ∷ᵃ lem-QVQ-at13213442 ∷ᵃ lem-QVQ-at1331 ∷ᵃ lem-QVQ-at14213243 ∷ᵃ lem-QVQ-at143143 ∷ᵃ lem-QVQ-at1441 ∷ᵃ lem-QVQ-at2332 ∷ᵃ lem-QVQ-at233442 ∷ᵃ lem-QVQ-at243243 ∷ᵃ lem-QVQ-at2442 ∷ᵃ lem-QVQ-at3443 ∷ᵃ lem-SWbc-box ∷ᵃ lem-SWbc-box-at0210233441 ∷ᵃ lem-SWbc-box-at0210243143 ∷ᵃ lem-SWbc-box-at02102441 ∷ᵃ lem-SWbc-box-at0213213440 ∷ᵃ lem-SWbc-box-at0214203143 ∷ᵃ lem-SWbc-box-at02142041 ∷ᵃ lem-SWbc-box-at0214213043 ∷ᵃ lem-SWbc-box-at022330 ∷ᵃ lem-SWbc-box-at02233440 ∷ᵃ lem-SWbc-box-at022440 ∷ᵃ lem-SWbc-box-at0310243142 ∷ᵃ lem-SWbc-box-at0310243241 ∷ᵃ lem-SWbc-box-at031031 ∷ᵃ lem-SWbc-box-at03103441 ∷ᵃ lem-SWbc-box-at0312203441 ∷ᵃ lem-SWbc-box-at0312213440 ∷ᵃ lem-SWbc-box-at0312243041 ∷ᵃ lem-SWbc-box-at0312243140 ∷ᵃ lem-SWbc-box-at0314203142 ∷ᵃ lem-SWbc-box-at0314213042 ∷ᵃ lem-SWbc-box-at0314213240 ∷ᵃ lem-SWbc-box-at03143041 ∷ᵃ lem-SWbc-box-at03143140 ∷ᵃ lem-SWbc-box-at03243240 ∷ᵃ lem-SWbc-box-at0330 ∷ᵃ lem-SWbc-box-at033440 ∷ᵃ lem-SWbc-box-at043043 ∷ᵃ lem-SWbc-box-at1221 ∷ᵃ lem-SWbc-box-at12213443 ∷ᵃ lem-SWbc-box-at122331 ∷ᵃ lem-SWbc-box-at12233441 ∷ᵃ lem-SWbc-box-at12243143 ∷ᵃ lem-SWbc-box-at122441 ∷ᵃ lem-SWbc-box-at132132 ∷ᵃ lem-SWbc-box-at13213442 ∷ᵃ lem-SWbc-box-at1331 ∷ᵃ lem-SWbc-box-at133441 ∷ᵃ lem-SWbc-box-at14213243 ∷ᵃ lem-SWbc-box-at143143 ∷ᵃ lem-SWbc-box-at1441 ∷ᵃ lem-SWbc-box-at2332 ∷ᵃ lem-SWbc-box-at233442 ∷ᵃ lem-SWbc-box-at243243 ∷ᵃ lem-SWbc-box-at2442 ∷ᵃ lem-SWbc-box-at3443 ∷ᵃ lem-XCSX-box-2-at0210243143 ∷ᵃ lem-XCSX-box-2-at122441 ∷ᵃ lem-XCSX-box-2-at243243 ∷ᵃ lem-box-cP-at021021 ∷ᵃ lem-box-cP-at0210213443 ∷ᵃ lem-box-cP-at0213243140 ∷ᵃ lem-box-cP-at0220 ∷ᵃ lem-box-cP-at03102132 ∷ᵃ lem-box-cP-at032032 ∷ᵃ lem-box-cP-at0410213243 ∷ᵃ lem-box-cP-at13243142 ∷ᵃ lem-box-cP-at13243241 ∷ᵃ lem-box-cP-at14233142 ∷ᵃ lem-box-cP-at14233241 ∷ᵃ lem-sym-bc-at03102132 ∷ᵃ lem-sym-bc-at0310213442 ∷ᵃ lem-sym-bc-at032032 ∷ᵃ lem-sym-bc-at04203243 ∷ᵃ lem-sym-bc-at13243142 ∷ᵃ lem-QVQ-at02132031 ∷ᵃ lem-QVQ-at02132130 ∷ᵃ lem-QVQ-at03122031 ∷ᵃ lem-QVQ-at03122130 ∷ᵃ lem-QVQ-at03143041 ∷ᵃ lem-SWbc-box-at02132031 ∷ᵃ lem-SWbc-box-at02132130 ∷ᵃ lem-SWbc-box-at03122031 ∷ᵃ lem-SWbc-box-at03122130 ∷ᵃ lem-SWbc-box-at0314203241 ∷ᵃ lem-box-cP-at0213243041 ∷ᵃ lem-box-cP-at0214233041 ∷ᵃ lem-box-cP-at0310213442 ∷ᵃ lem-sym-bc-at0214233041 ∷ᵃ nil
lem-box-cP : _
lem-box-cP = D016.lem-box-cP sD016
lem-box-cP-at0210243143 : _
lem-box-cP-at0210243143 = D016.lem-box-cP-at0210243143 sD016
lem-box-cP-at243243 : _
lem-box-cP-at243243 = D016.lem-box-cP-at243243 sD016
lem-box-cP-at122441 : _
lem-box-cP-at122441 = D016.lem-box-cP-at122441 sD016
lem-sym-bc : _
lem-sym-bc = D016.lem-sym-bc sD016
lem-sym-bc-at1221 : _
lem-sym-bc-at1221 = D016.lem-sym-bc-at1221 sD016
lem-box-cP-at1221 : _
lem-box-cP-at1221 = D016.lem-box-cP-at1221 sD016
lem-box-cP-at2332 : _
lem-box-cP-at2332 = D016.lem-box-cP-at2332 sD016
lem-box-cP-at122331 : _
lem-box-cP-at122331 = D016.lem-box-cP-at122331 sD016
lem-box-cP-at132132 : _
lem-box-cP-at132132 = D016.lem-box-cP-at132132 sD016
lem-sym-bc-at12243143 : _
lem-sym-bc-at12243143 = D016.lem-sym-bc-at12243143 sD016
lem-pairs-at14233142 : _
lem-pairs-at14233142 = D016.lem-pairs-at14233142 sD016
lem-box-cP-at13213442 : _
lem-box-cP-at13213442 = D016.lem-box-cP-at13213442 sD016
lem-box-cP-at1331 : _
lem-box-cP-at1331 = D016.lem-box-cP-at1331 sD016
lem-box-cP-at0110 : _
lem-box-cP-at0110 = D016.lem-box-cP-at0110 sD016
lem-sym-bc-at133441 : _
lem-sym-bc-at133441 = D016.lem-sym-bc-at133441 sD016
lem-pairs-at13243241 : _
lem-pairs-at13243241 = D016.lem-pairs-at13243241 sD016
lem-sym-bc-at13213442 : _
lem-sym-bc-at13213442 = D016.lem-sym-bc-at13213442 sD016
lem-pairs-at13243142 : _
lem-pairs-at13243142 = D016.lem-pairs-at13243142 sD016
lem-box-cP-at3443 : _
lem-box-cP-at3443 = D016.lem-box-cP-at3443 sD016
lem-box-cP-at043043 : _
lem-box-cP-at043043 = D016.lem-box-cP-at043043 sD016
lem-sym-bc-at043043 : _
lem-sym-bc-at043043 = D016.lem-sym-bc-at043043 sD016
lem-box-cP-at0330 : _
lem-box-cP-at0330 = D016.lem-box-cP-at0330 sD016
lem-box-cP-at0314203142 : _
lem-box-cP-at0314203142 = D016.lem-box-cP-at0314203142 sD016
lem-box-cP-at0310243142 : _
lem-box-cP-at0310243142 = D016.lem-box-cP-at0310243142 sD016
lem-box-perm-2314-at0410213243 : _
lem-box-perm-2314-at0410213243 = D016.lem-box-perm-2314-at0410213243 sD016
lem-box-perm-2314-at03102132 : _
lem-box-perm-2314-at03102132 = D016.lem-box-perm-2314-at03102132 sD016
lem-sym-bc-at0330 : _
lem-sym-bc-at0330 = D016.lem-sym-bc-at0330 sD016
lem-CXu-box-4-at03102132 : _
lem-CXu-box-4-at03102132 = D016.lem-CXu-box-4-at03102132 sD016
lem-F4-S0-CS1 : _
lem-F4-S0-CS1 = D016.lem-F4-S0-CS1 sD016
lem-F4-S0-CS2 : _
lem-F4-S0-CS2 = D016.lem-F4-S0-CS2 sD016
lem-F4-S2-CS0 : _
lem-F4-S2-CS0 = D016.lem-F4-S2-CS0 sD016
lem-sym-bc-at0214203143 : _
lem-sym-bc-at0214203143 = D016.lem-sym-bc-at0214203143 sD016
lem-box-cP-at0214213043 : _
lem-box-cP-at0214213043 = D016.lem-box-cP-at0214213043 sD016
lem-box-cP-at0210233441 : _
lem-box-cP-at0210233441 = D016.lem-box-cP-at0210233441 sD016
lem-sym-bc-at122441 : _
lem-sym-bc-at122441 = D016.lem-sym-bc-at122441 sD016
lem-box-cP-at12233441 : _
lem-box-cP-at12233441 = D016.lem-box-cP-at12233441 sD016
lem-sym-bc-at14213243 : _
lem-sym-bc-at14213243 = D016.lem-sym-bc-at14213243 sD016
lem-box-cP-at143143 : _
lem-box-cP-at143143 = D016.lem-box-cP-at143143 sD016
lem-box-cP-at233442 : _
lem-box-cP-at233442 = D016.lem-box-cP-at233442 sD016
lem-sym-bc-at0210243143 : _
lem-sym-bc-at0210243143 = D016.lem-sym-bc-at0210243143 sD016
lem-sym-bc-at243243 : _
lem-sym-bc-at243243 = D016.lem-sym-bc-at243243 sD016
lem-sym-bc-at1441 : _
lem-sym-bc-at1441 = D016.lem-sym-bc-at1441 sD016
lem-pairs-at14233241 : _
lem-pairs-at14233241 = D016.lem-pairs-at14233241 sD016
lem-box-cP-at12213443 : _
lem-box-cP-at12213443 = D016.lem-box-cP-at12213443 sD016
lem-sym-bc-at0314213042 : _
lem-sym-bc-at0314213042 = D016.lem-sym-bc-at0314213042 sD016
lem-box-cP-at0213203441 : _
lem-box-cP-at0213203441 = D016.lem-box-cP-at0213203441 sD016
lem-sym-bc-at0314203142 : _
lem-sym-bc-at0314203142 = D016.lem-sym-bc-at0314203142 sD016
lem-box-cP-at0314213042 : _
lem-box-cP-at0314213042 = D016.lem-box-cP-at0314213042 sD016
lem-sym-bc-at0214213043 : _
lem-sym-bc-at0214213043 = D016.lem-sym-bc-at0214213043 sD016
lem-sym-bc-at1331 : _
lem-sym-bc-at1331 = D016.lem-sym-bc-at1331 sD016
lem-pairs-at032032 : _
lem-pairs-at032032 = D016.lem-pairs-at032032 sD016
lem-sym-bc-at0312243140 : _
lem-sym-bc-at0312243140 = D016.lem-sym-bc-at0312243140 sD016
lem-sym-bc-at0312213440 : _
lem-sym-bc-at0312213440 = D016.lem-sym-bc-at0312213440 sD016
lem-box-cP-at0312243140 : _
lem-box-cP-at0312243140 = D016.lem-box-cP-at0312243140 sD016
lem-sym-bc-at132132 : _
lem-sym-bc-at132132 = D016.lem-sym-bc-at132132 sD016
lem-sym-bc-at022330 : _
lem-sym-bc-at022330 = D016.lem-sym-bc-at022330 sD016
lem-pairs-at0220 : _
lem-pairs-at0220 = D016.lem-pairs-at0220 sD016
lem-sym-bc-at0213213440 : _
lem-sym-bc-at0213213440 = D016.lem-sym-bc-at0213213440 sD016
lem-pairs-at0213243140 : _
lem-pairs-at0213243140 = D016.lem-pairs-at0213243140 sD016
lem-box-cP-at022330 : _
lem-box-cP-at022330 = D016.lem-box-cP-at022330 sD016
lem-sym-bc-at122331 : _
lem-sym-bc-at122331 = D016.lem-sym-bc-at122331 sD016
lem-box-cP-at14213243 : _
lem-box-cP-at14213243 = D016.lem-box-cP-at14213243 sD016
lem-sym-bc-at12233441 : _
lem-sym-bc-at12233441 = D016.lem-sym-bc-at12233441 sD016
lem-sym-bc-at2332 : _
lem-sym-bc-at2332 = D016.lem-sym-bc-at2332 sD016
lem-box-perm-1324-at03102132 : _
lem-box-perm-1324-at03102132 = D016.lem-box-perm-1324-at03102132 sD016
lem-box-cP-at0214203143 : _
lem-box-cP-at0214203143 = D016.lem-box-cP-at0214203143 sD016
lem-sym-bc-at02233440 : _
lem-sym-bc-at02233440 = D016.lem-sym-bc-at02233440 sD016
lem-box-cP-at022440 : _
lem-box-cP-at022440 = D016.lem-box-cP-at022440 sD016
lem-sym-bc-at022440 : _
lem-sym-bc-at022440 = D016.lem-sym-bc-at022440 sD016
lem-box-cP-at02233440 : _
lem-box-cP-at02233440 = D016.lem-box-cP-at02233440 sD016
lem-box-cP-at1441 : _
lem-box-cP-at1441 = D016.lem-box-cP-at1441 sD016
lem-Xb-box-at13243142 : _
lem-Xb-box-at13243142 = D016.lem-Xb-box-at13243142 sD016
lem-box-perm-1324-at13243142 : _
lem-box-perm-1324-at13243142 = D016.lem-box-perm-1324-at13243142 sD016
lem-sym-bc-at0210233441 : _
lem-sym-bc-at0210233441 = D016.lem-sym-bc-at0210233441 sD016
lem-box-cP-at02102441 : _
lem-box-cP-at02102441 = D016.lem-box-cP-at02102441 sD016
lem-sym-bc-at02102441 : _
lem-sym-bc-at02102441 = D016.lem-sym-bc-at02102441 sD016
lem-sym-bc-at233442 : _
lem-sym-bc-at233442 = D016.lem-sym-bc-at233442 sD016
lem-box-cP-at2442 : _
lem-box-cP-at2442 = D016.lem-box-cP-at2442 sD016
lem-sym-bc-at2442 : _
lem-sym-bc-at2442 = D016.lem-sym-bc-at2442 sD016
lem-sym-bc-at143143 : _
lem-sym-bc-at143143 = D016.lem-sym-bc-at143143 sD016
lem-sym-bc-at12213443 : _
lem-sym-bc-at12213443 = D016.lem-sym-bc-at12213443 sD016
lem-box-cP-at12243143 : _
lem-box-cP-at12243143 = D016.lem-box-cP-at12243143 sD016
lem-sym-bc-at03143140 : _
lem-sym-bc-at03143140 = D016.lem-sym-bc-at03143140 sD016
lem-box-cP-at0314213240 : _
lem-box-cP-at0314213240 = D016.lem-box-cP-at0314213240 sD016
lem-sym-bc-at0314213240 : _
lem-sym-bc-at0314213240 = D016.lem-sym-bc-at0314213240 sD016
lem-box-cP-at03143140 : _
lem-box-cP-at03143140 = D016.lem-box-cP-at03143140 sD016
lem-box-cP-at03243240 : _
lem-box-cP-at03243240 = D016.lem-box-cP-at03243240 sD016
lem-sym-bc-at033440 : _
lem-sym-bc-at033440 = D016.lem-sym-bc-at033440 sD016
lem-sym-bc-at03243240 : _
lem-sym-bc-at03243240 = D016.lem-sym-bc-at03243240 sD016
lem-box-cP-at033440 : _
lem-box-cP-at033440 = D016.lem-box-cP-at033440 sD016
lem-sym-bc-at03103441 : _
lem-sym-bc-at03103441 = D016.lem-sym-bc-at03103441 sD016
lem-box-cP-at0310243241 : _
lem-box-cP-at0310243241 = D016.lem-box-cP-at0310243241 sD016
lem-sym-bc-at0310243241 : _
lem-sym-bc-at0310243241 = D016.lem-sym-bc-at0310243241 sD016
lem-box-cP-at03103441 : _
lem-box-cP-at03103441 = D016.lem-box-cP-at03103441 sD016
lem-sym-bc-at0310243142 : _
lem-sym-bc-at0310243142 = D016.lem-sym-bc-at0310243142 sD016
lem-box-perm-1324-at0310213442 : _
lem-box-perm-1324-at0310213442 = D016.lem-box-perm-1324-at0310213442 sD016
lem-sym-bc-at0312203441 : _
lem-sym-bc-at0312203441 = D016.lem-sym-bc-at0312203441 sD016
lem-box-cP-at0312243041 : _
lem-box-cP-at0312243041 = D016.lem-box-cP-at0312243041 sD016
lem-sym-bc-at0312243041 : _
lem-sym-bc-at0312243041 = D016.lem-sym-bc-at0312243041 sD016
lem-box-cP-at0312203441 : _
lem-box-cP-at0312203441 = D016.lem-box-cP-at0312203441 sD016
lem-sym-bc-at3443 : _
lem-sym-bc-at3443 = D016.lem-sym-bc-at3443 sD016
lem-sym-bc-at031031 : _
lem-sym-bc-at031031 = D016.lem-sym-bc-at031031 sD016
lem-box-cP-at031031 : _
lem-box-cP-at031031 = D016.lem-box-cP-at031031 sD016
lem-pairs-at03102132 : _
lem-pairs-at03102132 = D016.lem-pairs-at03102132 sD016
lem-sym-bc-at03143041 : _
lem-sym-bc-at03143041 = D016.lem-sym-bc-at03143041 sD016
lem-sym-bc-at02142041 : _
lem-sym-bc-at02142041 = D016.lem-sym-bc-at02142041 sD016
lem-sym-bc-at0314203241 : _
lem-sym-bc-at0314203241 = D016.lem-sym-bc-at0314203241 sD016
lem-pairs-at0214233041 : _
lem-pairs-at0214233041 = D016.lem-pairs-at0214233041 sD016
lem-pairs-at0210213443 : _
lem-pairs-at0210213443 = D016.lem-pairs-at0210213443 sD016
lem-box-perm-2314-at0213243041 : _
lem-box-perm-2314-at0213243041 = D016.lem-box-perm-2314-at0213243041 sD016
lem-sym-bc-at02132130 : _
lem-sym-bc-at02132130 = D016.lem-sym-bc-at02132130 sD016
lem-box-cP-at03143041 : _
lem-box-cP-at03143041 = D016.lem-box-cP-at03143041 sD016
lem-box-cP-at02132031 : _
lem-box-cP-at02132031 = D016.lem-box-cP-at02132031 sD016
lem-pairs-at0310213442 : _
lem-pairs-at0310213442 = D016.lem-pairs-at0310213442 sD016
lem-sym-bc-at02132031 : _
lem-sym-bc-at02132031 = D016.lem-sym-bc-at02132031 sD016
lem-box-cP-at02132130 : _
lem-box-cP-at02132130 = D016.lem-box-cP-at02132130 sD016
lem-pairs-at0213243041 : _
lem-pairs-at0213243041 = D016.lem-pairs-at0213243041 sD016
lem-sym-bc-at03122130 : _
lem-sym-bc-at03122130 = D016.lem-sym-bc-at03122130 sD016
lem-pairs-at021021 : _
lem-pairs-at021021 = D016.lem-pairs-at021021 sD016
lem-box-cP-at03122031 : _
lem-box-cP-at03122031 = D016.lem-box-cP-at03122031 sD016
lem-sym-bc-at03122031 : _
lem-sym-bc-at03122031 = D016.lem-sym-bc-at03122031 sD016
lem-box-cP-at03122130 : _
lem-box-cP-at03122130 = D016.lem-box-cP-at03122130 sD016
sD018 : SD018
sD018 = lem-sym-ab ∷ᵃ lem-sym-ab-at032032 ∷ᵃ lem-sym-ab-at04203243 ∷ᵃ lem-sym-ab-at1221 ∷ᵃ lem-sym-ab-at122331 ∷ᵃ lem-sym-ab-at12233441 ∷ᵃ lem-sym-ab-at122441 ∷ᵃ lem-sym-ab-at2332 ∷ᵃ lem-sym-ab-at233442 ∷ᵃ lem-box-tQ-at0410213243 ∷ᵃ lem-box-tQ-at13243142 ∷ᵃ lem-box-tQ-at13243241 ∷ᵃ lem-box-tQ-at14233142 ∷ᵃ lem-box-tQ ∷ᵃ lem-box-tQ-at0210233441 ∷ᵃ lem-box-tQ-at0210243143 ∷ᵃ lem-box-tQ-at0310243142 ∷ᵃ lem-box-tQ-at0330 ∷ᵃ lem-box-tQ-at043043 ∷ᵃ lem-box-tQ-at12243143 ∷ᵃ lem-box-tQ-at122441 ∷ᵃ lem-box-tQ-at1441 ∷ᵃ lem-box-tQ-at233442 ∷ᵃ lem-box-tQ-at243243 ∷ᵃ lem-box-tQ-at2442 ∷ᵃ lem-P-box ∷ᵃ lem-P-box-at0214213043 ∷ᵃ lem-P-box-at0310243142 ∷ᵃ lem-P-box-at0330 ∷ᵃ lem-P-box-at1221 ∷ᵃ lem-P-box-at122331 ∷ᵃ lem-P-box-at132132 ∷ᵃ lem-P-box-at13213442 ∷ᵃ lem-P-box-at1331 ∷ᵃ lem-P-box-at2332 ∷ᵃ lem-P-box-at3443 ∷ᵃ lem-t-cP ∷ᵃ lem-t-cP-at0210243143 ∷ᵃ lem-t-cP-at043043 ∷ᵃ lem-t-cP-at122441 ∷ᵃ lem-t-cP-at243243 ∷ᵃ lem-P-box-at143143 ∷ᵃ lem-CXu-box-4-at03102132 ∷ᵃ lem-box-cP ∷ᵃ lem-box-cP-at0210243143 ∷ᵃ lem-box-cP-at0214213043 ∷ᵃ lem-box-cP-at0310243142 ∷ᵃ lem-box-cP-at0314203142 ∷ᵃ lem-box-cP-at0330 ∷ᵃ lem-box-cP-at043043 ∷ᵃ lem-box-cP-at1221 ∷ᵃ lem-box-cP-at122331 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-cP-at132132 ∷ᵃ lem-box-cP-at13213442 ∷ᵃ lem-box-cP-at1331 ∷ᵃ lem-box-cP-at143143 ∷ᵃ lem-box-cP-at2332 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-box-cP-at3443 ∷ᵃ lem-pairs-at13243142 ∷ᵃ lem-pairs-at13243241 ∷ᵃ lem-pairs-at14233241 ∷ᵃ lem-sym-bc ∷ᵃ lem-sym-bc-at0210243143 ∷ᵃ lem-sym-bc-at0330 ∷ᵃ lem-sym-bc-at043043 ∷ᵃ lem-sym-bc-at1221 ∷ᵃ lem-sym-bc-at122441 ∷ᵃ lem-sym-bc-at13213442 ∷ᵃ lem-sym-bc-at133441 ∷ᵃ lem-sym-bc-at1441 ∷ᵃ lem-sym-bc-at243243 ∷ᵃ nil
lem-box2 : _
lem-box2 = D018.lem-box2 sD018
lem-Xb-box-at0210243143 : _
lem-Xb-box-at0210243143 = D018.lem-Xb-box-at0210243143 sD018
lem-box2-at0210243143 : _
lem-box2-at0210243143 = D018.lem-box2-at0210243143 sD018
lem-Xb-box-at243243 : _
lem-Xb-box-at243243 = D018.lem-Xb-box-at243243 sD018
lem-box2-at243243 : _
lem-box2-at243243 = D018.lem-box2-at243243 sD018
lem-Xb-box-at122441 : _
lem-Xb-box-at122441 = D018.lem-Xb-box-at122441 sD018
lem-box2-at122441 : _
lem-box2-at122441 = D018.lem-box2-at122441 sD018
lem-pairs : _
lem-pairs = D018.lem-pairs sD018
lem-box-perm-1324 : _
lem-box-perm-1324 = D018.lem-box-perm-1324 sD018
lem-pairs-at1221 : _
lem-pairs-at1221 = D018.lem-pairs-at1221 sD018
lem-box-perm-3124 : _
lem-box-perm-3124 = D018.lem-box-perm-3124 sD018
lem-pairs-at2332 : _
lem-pairs-at2332 = D018.lem-pairs-at2332 sD018
lem-pairs-at122331 : _
lem-pairs-at122331 = D018.lem-pairs-at122331 sD018
lem-pairs-at132132 : _
lem-pairs-at132132 = D018.lem-pairs-at132132 sD018
lem-pairs-at13213442 : _
lem-pairs-at13213442 = D018.lem-pairs-at13213442 sD018
lem-pairs-at1331 : _
lem-pairs-at1331 = D018.lem-pairs-at1331 sD018
lem-Ku-box : _
lem-Ku-box = D018.lem-Ku-box sD018
lem-Kdu-box : _
lem-Kdu-box = D018.lem-Kdu-box sD018
lem-CSu-box-3 : _
lem-CSu-box-3 = D018.lem-CSu-box-3 sD018
lem-CSdu-box-3 : _
lem-CSdu-box-3 = D018.lem-CSdu-box-3 sD018
lem-CSu-box-4 : _
lem-CSu-box-4 = D018.lem-CSu-box-4 sD018
lem-CSdu-box-4 : _
lem-CSdu-box-4 = D018.lem-CSdu-box-4 sD018
lem-box-perm-4123-at12233441 : _
lem-box-perm-4123-at12233441 = D018.lem-box-perm-4123-at12233441 sD018
lem-box-perm-1423-at233442 : _
lem-box-perm-1423-at233442 = D018.lem-box-perm-1423-at233442 sD018
lem-pairs-at3443 : _
lem-pairs-at3443 = D018.lem-pairs-at3443 sD018
lem-CSdu-box-3-at043043 : _
lem-CSdu-box-3-at043043 = D018.lem-CSdu-box-3-at043043 sD018
lem-box-perm-1324-at043043 : _
lem-box-perm-1324-at043043 = D018.lem-box-perm-1324-at043043 sD018
lem-box-perm-3124-at043043 : _
lem-box-perm-3124-at043043 = D018.lem-box-perm-3124-at043043 sD018
lem-pairs-at0330 : _
lem-pairs-at0330 = D018.lem-pairs-at0330 sD018
lem-box-box-4-at0410213243 : _
lem-box-box-4-at0410213243 = D018.lem-box-box-4-at0410213243 sD018
lem-pairs-at0310243142 : _
lem-pairs-at0310243142 = D018.lem-pairs-at0310243142 sD018
lem-CSu-box-3-at043043 : _
lem-CSu-box-3-at043043 = D018.lem-CSu-box-3-at043043 sD018
lem-box2-at043043 : _
lem-box2-at043043 = D018.lem-box2-at043043 sD018
lem-box-perm-3124-at0330 : _
lem-box-perm-3124-at0330 = D018.lem-box-perm-3124-at0330 sD018
lem-CXAu-S : _
lem-CXAu-S = D018.lem-CXAu-S sD018
lem-F4-I-CS0 : _
lem-F4-I-CS0 = D018.lem-F4-I-CS0 sD018
lem-F4-I-CS1 : _
lem-F4-I-CS1 = D018.lem-F4-I-CS1 sD018
lem-F4-I-CS2 : _
lem-F4-I-CS2 = D018.lem-F4-I-CS2 sD018
lem-F4-S0-CS0 : _
lem-F4-S0-CS0 = D018.lem-F4-S0-CS0 sD018
lem-F4-S1-CS0 : _
lem-F4-S1-CS0 = D018.lem-F4-S1-CS0 sD018
lem-F4-S1-CS1 : _
lem-F4-S1-CS1 = D018.lem-F4-S1-CS1 sD018
lem-F4-S1-CS2 : _
lem-F4-S1-CS2 = D018.lem-F4-S1-CS2 sD018
lem-F4-S2-CS1 : _
lem-F4-S2-CS1 = D018.lem-F4-S2-CS1 sD018
lem-F4-S2-CS2 : _
lem-F4-S2-CS2 = D018.lem-F4-S2-CS2 sD018
lem-F4-S3-CS0 : _
lem-F4-S3-CS0 = D018.lem-F4-S3-CS0 sD018
lem-F4-S3-CS1 : _
lem-F4-S3-CS1 = D018.lem-F4-S3-CS1 sD018
lem-F4-S3-CS2 : _
lem-F4-S3-CS2 = D018.lem-F4-S3-CS2 sD018
lem-F4-K0-CS0 : _
lem-F4-K0-CS0 = D018.lem-F4-K0-CS0 sD018
lem-Ku-box-at243243 : _
lem-Ku-box-at243243 = D018.lem-Ku-box-at243243 sD018
lem-Kdu-box-at243243 : _
lem-Kdu-box-at243243 = D018.lem-Kdu-box-at243243 sD018
lem-Ku-box-at122441 : _
lem-Ku-box-at122441 = D018.lem-Ku-box-at122441 sD018
lem-Kdu-box-at122441 : _
lem-Kdu-box-at122441 = D018.lem-Kdu-box-at122441 sD018
lem-pairs-at0214213043 : _
lem-pairs-at0214213043 = D018.lem-pairs-at0214213043 sD018
lem-F4-K1-CS1 : _
lem-F4-K1-CS1 = D018.lem-F4-K1-CS1 sD018
lem-box-perm-1324-at122441 : _
lem-box-perm-1324-at122441 = D018.lem-box-perm-1324-at122441 sD018
lem-Ku-box-at0210243143 : _
lem-Ku-box-at0210243143 = D018.lem-Ku-box-at0210243143 sD018
lem-Kdu-box-at0210243143 : _
lem-Kdu-box-at0210243143 = D018.lem-Kdu-box-at0210243143 sD018
lem-pairs-at143143 : _
lem-pairs-at143143 = D018.lem-pairs-at143143 sD018
lem-F4-K2-CS2 : _
lem-F4-K2-CS2 = D018.lem-F4-K2-CS2 sD018
lem-box-perm-1324-at0210243143 : _
lem-box-perm-1324-at0210243143 = D018.lem-box-perm-1324-at0210243143 sD018
lem-box-perm-1324-at243243 : _
lem-box-perm-1324-at243243 = D018.lem-box-perm-1324-at243243 sD018
lem-box-perm-1423-at122441 : _
lem-box-perm-1423-at122441 = D018.lem-box-perm-1423-at122441 sD018
lem-F4-CS0-I : _
lem-F4-CS0-I = D018.lem-F4-CS0-I sD018
lem-F4-CS0-S0 : _
lem-F4-CS0-S0 = D018.lem-F4-CS0-S0 sD018
lem-F4-CS0-S1 : _
lem-F4-CS0-S1 = D018.lem-F4-CS0-S1 sD018
lem-F4-CS0-S3 : _
lem-F4-CS0-S3 = D018.lem-F4-CS0-S3 sD018
lem-F4-CS0-K0 : _
lem-F4-CS0-K0 = D018.lem-F4-CS0-K0 sD018
lem-F4-CS1-I : _
lem-F4-CS1-I = D018.lem-F4-CS1-I sD018
lem-F4-CS1-S1 : _
lem-F4-CS1-S1 = D018.lem-F4-CS1-S1 sD018
lem-F4-CS1-S2 : _
lem-F4-CS1-S2 = D018.lem-F4-CS1-S2 sD018
lem-F4-CS1-S3 : _
lem-F4-CS1-S3 = D018.lem-F4-CS1-S3 sD018
lem-F4-CS1-K1 : _
lem-F4-CS1-K1 = D018.lem-F4-CS1-K1 sD018
lem-F4-CS2-I : _
lem-F4-CS2-I = D018.lem-F4-CS2-I sD018
lem-F4-CS2-S1 : _
lem-F4-CS2-S1 = D018.lem-F4-CS2-S1 sD018
lem-F4-CS2-S2 : _
lem-F4-CS2-S2 = D018.lem-F4-CS2-S2 sD018
lem-F4-CS2-S3 : _
lem-F4-CS2-S3 = D018.lem-F4-CS2-S3 sD018
sD019 : SD019
sD019 = lem-sym-ab-at0210243143 ∷ᵃ lem-sym-ab-at0214203143 ∷ᵃ lem-sym-ab-at03102132 ∷ᵃ lem-sym-ab-at0310243142 ∷ᵃ lem-sym-ab-at0312213440 ∷ᵃ lem-sym-ab-at0314203142 ∷ᵃ lem-sym-ab-at122441 ∷ᵃ lem-sym-ab-at021021 ∷ᵃ lem-sym-ab-at0213213440 ∷ᵃ lem-sym-ab-at0220 ∷ᵃ lem-sym-ab-at02233440 ∷ᵃ lem-sym-ab-at14233241 ∷ᵃ lem-box-tQ-at032032 ∷ᵃ lem-box-tQ-at0210243143 ∷ᵃ lem-box-tQ-at0214213043 ∷ᵃ lem-box-tQ-at022330 ∷ᵃ lem-box-tQ-at0310243142 ∷ᵃ lem-box-tQ-at0314213042 ∷ᵃ lem-box-tQ-at122331 ∷ᵃ lem-P-box-at0210233441 ∷ᵃ lem-P-box-at0210243143 ∷ᵃ lem-P-box-at022330 ∷ᵃ lem-P-box-at0312243140 ∷ᵃ lem-P-box-at243243 ∷ᵃ lem-t-cP-at0314213042 ∷ᵃ lem-sym-bc-at0213243140 ∷ᵃ lem-box-cP-at0210233441 ∷ᵃ lem-box-cP-at0210243143 ∷ᵃ lem-box-cP-at0213203441 ∷ᵃ lem-box-cP-at022330 ∷ᵃ lem-box-cP-at0310243142 ∷ᵃ lem-box-cP-at0312243140 ∷ᵃ lem-box-cP-at0314213042 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-pairs-at0213243140 ∷ᵃ lem-pairs-at0220 ∷ᵃ lem-pairs-at032032 ∷ᵃ lem-pairs-at13243241 ∷ᵃ lem-sym-bc-at0213213440 ∷ᵃ lem-sym-bc-at0214203143 ∷ᵃ lem-sym-bc-at0214213043 ∷ᵃ lem-sym-bc-at0312243140 ∷ᵃ lem-sym-bc-at0314203142 ∷ᵃ lem-sym-bc-at0314213042 ∷ᵃ lem-sym-bc-at1441 ∷ᵃ nil
lem-F4-CS2-K2 : _
lem-F4-CS2-K2 = D019.lem-F4-CS2-K2 sD019
lem-F4-CS0-CS0 : _
lem-F4-CS0-CS0 = D019.lem-F4-CS0-CS0 sD019
lem-box-perm-2314-at0210243143 : _
lem-box-perm-2314-at0210243143 = D019.lem-box-perm-2314-at0210243143 sD019
lem-box-perm-1324-at0314213042 : _
lem-box-perm-1324-at0314213042 = D019.lem-box-perm-1324-at0314213042 sD019
lem-box-perm-3124-at0314213042 : _
lem-box-perm-3124-at0314213042 = D019.lem-box-perm-3124-at0314213042 sD019
lem-box-box-4-at0310243142 : _
lem-box-box-4-at0310243142 = D019.lem-box-box-4-at0310243142 sD019
lem-pairs-at0210233441 : _
lem-pairs-at0210233441 = D019.lem-pairs-at0210233441 sD019
lem-box-perm-2314-at0310243142 : _
lem-box-perm-2314-at0310243142 = D019.lem-box-perm-2314-at0310243142 sD019
lem-CSdu-box-3-at0314213042 : _
lem-CSdu-box-3-at0314213042 = D019.lem-CSdu-box-3-at0314213042 sD019
lem-CSu-box-3-at0314213042 : _
lem-CSu-box-3-at0314213042 = D019.lem-CSu-box-3-at0314213042 sD019
lem-box2-at0314213042 : _
lem-box2-at0314213042 = D019.lem-box2-at0314213042 sD019
lem-box-perm-3124-at0214213043 : _
lem-box-perm-3124-at0214213043 = D019.lem-box-perm-3124-at0214213043 sD019
lem-CXu-box-4-at0210243143 : _
lem-CXu-box-4-at0210243143 = D019.lem-CXu-box-4-at0210243143 sD019
lem-CSdu-box-3-at243243 : _
lem-CSdu-box-3-at243243 = D019.lem-CSdu-box-3-at243243 sD019
lem-CSu-box-3-at243243 : _
lem-CSu-box-3-at243243 = D019.lem-CSu-box-3-at243243 sD019
lem-pairs-at243243 : _
lem-pairs-at243243 = D019.lem-pairs-at243243 sD019
lem-box-perm-2341-at03102132 : _
lem-box-perm-2341-at03102132 = D019.lem-box-perm-2341-at03102132 sD019
lem-pairs-at0312243140 : _
lem-pairs-at0312243140 = D019.lem-pairs-at0312243140 sD019
lem-CXu-box-4-at0310243142 : _
lem-CXu-box-4-at0310243142 = D019.lem-CXu-box-4-at0310243142 sD019
lem-CSu-box-3-at0310243142 : _
lem-CSu-box-3-at0310243142 = D019.lem-CSu-box-3-at0310243142 sD019
lem-CSdu-box-3-at0310243142 : _
lem-CSdu-box-3-at0310243142 = D019.lem-CSdu-box-3-at0310243142 sD019
lem-CSdu-box-3-at122441 : _
lem-CSdu-box-3-at122441 = D019.lem-CSdu-box-3-at122441 sD019
lem-CSu-box-3-at122441 : _
lem-CSu-box-3-at122441 = D019.lem-CSu-box-3-at122441 sD019
lem-pairs-at0210243143 : _
lem-pairs-at0210243143 = D019.lem-pairs-at0210243143 sD019
lem-box-perm-1432-at122441 : _
lem-box-perm-1432-at122441 = D019.lem-box-perm-1432-at122441 sD019
lem-box-perm-2341-at021021 : _
lem-box-perm-2341-at021021 = D019.lem-box-perm-2341-at021021 sD019
lem-box-perm-4123-at02233440 : _
lem-box-perm-4123-at02233440 = D019.lem-box-perm-4123-at02233440 sD019
lem-pairs-at022330 : _
lem-pairs-at022330 = D019.lem-pairs-at022330 sD019
lem-CSu-box-3-at0210243143 : _
lem-CSu-box-3-at0210243143 = D019.lem-CSu-box-3-at0210243143 sD019
lem-CSdu-box-3-at0210243143 : _
lem-CSdu-box-3-at0210243143 = D019.lem-CSdu-box-3-at0210243143 sD019
sD020 : SD020
sD020 = lem-sym-ab-at132132 ∷ᵃ lem-box-tQ-at12233441 ∷ᵃ lem-box-tQ-at132132 ∷ᵃ lem-box-tQ-at14213243 ∷ᵃ lem-P-box-at12233441 ∷ᵃ lem-P-box-at122441 ∷ᵃ lem-P-box-at14213243 ∷ᵃ lem-box-cP-at0210243143 ∷ᵃ lem-box-cP-at12233441 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-cP-at14213243 ∷ᵃ lem-box-cP-at2332 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-box-perm-1324-at03102132 ∷ᵃ lem-sym-bc-at0330 ∷ᵃ lem-sym-bc-at2332 ∷ᵃ nil
lem-F4-CS1-CS1 : _
lem-F4-CS1-CS1 = D020.lem-F4-CS1-CS1 sD020
lem-pairs-at14213243 : _
lem-pairs-at14213243 = D020.lem-pairs-at14213243 sD020
lem-pairs-at12233441 : _
lem-pairs-at12233441 = D020.lem-pairs-at12233441 sD020
lem-pairs-at122441 : _
lem-pairs-at122441 = D020.lem-pairs-at122441 sD020
lem-F4-CS2-CS2 : _
lem-F4-CS2-CS2 = D020.lem-F4-CS2-CS2 sD020
lem-F2-I-CS0 : _
lem-F2-I-CS0 = D020.lem-F2-I-CS0 sD020
lem-F2-I-CS1 : _
lem-F2-I-CS1 = D020.lem-F2-I-CS1 sD020
lem-F2-I-CS2 : _
lem-F2-I-CS2 = D020.lem-F2-I-CS2 sD020
lem-F2-S1-CS2 : _
lem-F2-S1-CS2 = D020.lem-F2-S1-CS2 sD020
lem-F2-S3-CS0 : _
lem-F2-S3-CS0 = D020.lem-F2-S3-CS0 sD020
lem-F2-S3-CS1 : _
lem-F2-S3-CS1 = D020.lem-F2-S3-CS1 sD020
lem-CSu-box-4-at122441 : _
lem-CSu-box-4-at122441 = D020.lem-CSu-box-4-at122441 sD020
lem-box-perm-1324-at0330 : _
lem-box-perm-1324-at0330 = D020.lem-box-perm-1324-at0330 sD020
lem-box-perm-2314-at132132 : _
lem-box-perm-2314-at132132 = D020.lem-box-perm-2314-at132132 sD020
lem-Xb-box-at2332 : _
lem-Xb-box-at2332 = D020.lem-Xb-box-at2332 sD020
lem-box-perm-1324-at2332 : _
lem-box-perm-1324-at2332 = D020.lem-box-perm-1324-at2332 sD020
lem-nf-comm-CS-S0at0 : _
lem-nf-comm-CS-S0at0 = D020.lem-nf-comm-CS-S0at0 sD020
lem-nf-comm-CS-S0at1 : _
lem-nf-comm-CS-S0at1 = D020.lem-nf-comm-CS-S0at1 sD020
sD025 : SD025
sD025 = lem-sym-ab ∷ᵃ lem-sym-ab-at0210233441 ∷ᵃ lem-sym-ab-at0210243143 ∷ᵃ lem-sym-ab-at0213203441 ∷ᵃ lem-sym-ab-at03102132 ∷ᵃ lem-sym-ab-at0310243142 ∷ᵃ lem-sym-ab-at0314203142 ∷ᵃ lem-sym-ab-at032032 ∷ᵃ lem-sym-ab-at033440 ∷ᵃ lem-sym-ab-at1221 ∷ᵃ lem-sym-ab-at122331 ∷ᵃ lem-sym-ab-at12243143 ∷ᵃ lem-sym-ab-at13213442 ∷ᵃ lem-sym-ab-at13243142 ∷ᵃ lem-sym-ab-at13243241 ∷ᵃ lem-sym-ab-at133441 ∷ᵃ lem-sym-ab-at14233142 ∷ᵃ lem-sym-ab-at2332 ∷ᵃ lem-sym-ab-at243243 ∷ᵃ lem-sym-ab-at021021 ∷ᵃ lem-sym-ab-at0220 ∷ᵃ lem-sym-ab-at132132 ∷ᵃ lem-sym-ab-at1331 ∷ᵃ lem-sym-ab-at14213243 ∷ᵃ lem-box-tQ-at0314213042 ∷ᵃ lem-box-tQ-at043043 ∷ᵃ lem-box-tQ-at12233441 ∷ᵃ lem-box-tQ-at02233440 ∷ᵃ lem-CSdu-box-1 ∷ᵃ lem-CSdu-box-2 ∷ᵃ lem-CSdu-box-2-at0210243143 ∷ᵃ lem-CSdu-box-2-at122441 ∷ᵃ lem-CSdu-box-2-at243243 ∷ᵃ lem-CSu-box-1 ∷ᵃ lem-CSu-box-2 ∷ᵃ lem-CSu-box-2-at122441 ∷ᵃ lem-CSu-box-2-at243243 ∷ᵃ lem-Sdu-box ∷ᵃ lem-Su-box ∷ᵃ lem-CSu-box-2-at0210243143 ∷ᵃ lem-box-cP-at0210213443 ∷ᵃ lem-sym-bc-at0220 ∷ᵃ lem-sym-bc-at032032 ∷ᵃ lem-sym-bc-at13243142 ∷ᵃ lem-sym-bc-at13243241 ∷ᵃ lem-sym-bc-at14233142 ∷ᵃ lem-box-cP-at0210243143 ∷ᵃ lem-box-cP-at1221 ∷ᵃ lem-box-cP-at12213443 ∷ᵃ lem-box-cP-at12233441 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-box-cP-at3443 ∷ᵃ lem-pairs-at13243142 ∷ᵃ lem-pairs-at14233142 ∷ᵃ lem-sym-bc ∷ᵃ lem-sym-bc-at0214203143 ∷ᵃ lem-sym-bc-at022330 ∷ᵃ lem-sym-bc-at0312213440 ∷ᵃ lem-sym-bc-at0330 ∷ᵃ lem-sym-bc-at1221 ∷ᵃ lem-sym-bc-at122331 ∷ᵃ lem-sym-bc-at12233441 ∷ᵃ lem-sym-bc-at12243143 ∷ᵃ lem-sym-bc-at122441 ∷ᵃ lem-sym-bc-at132132 ∷ᵃ lem-sym-bc-at1331 ∷ᵃ lem-sym-bc-at14213243 ∷ᵃ lem-sym-bc-at2332 ∷ᵃ lem-CSdu-box-3 ∷ᵃ lem-CSdu-box-3-at043043 ∷ᵃ lem-CSdu-box-4 ∷ᵃ lem-CSu-box-3 ∷ᵃ lem-CSu-box-4 ∷ᵃ lem-Kdu-box ∷ᵃ lem-Kdu-box-at0210243143 ∷ᵃ lem-Kdu-box-at122441 ∷ᵃ lem-Kdu-box-at243243 ∷ᵃ lem-Ku-box ∷ᵃ lem-Ku-box-at0210243143 ∷ᵃ lem-Ku-box-at122441 ∷ᵃ lem-Ku-box-at243243 ∷ᵃ lem-Xb-box-at0210243143 ∷ᵃ lem-Xb-box-at122441 ∷ᵃ lem-Xb-box-at243243 ∷ᵃ lem-box-perm-1324-at0210243143 ∷ᵃ lem-box-perm-1324-at122441 ∷ᵃ lem-box-perm-1324-at243243 ∷ᵃ lem-box-perm-1423-at122441 ∷ᵃ lem-box2-at0210243143 ∷ᵃ lem-box2-at122441 ∷ᵃ lem-box2-at243243 ∷ᵃ lem-pairs ∷ᵃ lem-pairs-at0214213043 ∷ᵃ lem-pairs-at0310243142 ∷ᵃ lem-pairs-at0330 ∷ᵃ lem-pairs-at1221 ∷ᵃ lem-pairs-at122331 ∷ᵃ lem-pairs-at132132 ∷ᵃ lem-pairs-at13213442 ∷ᵃ lem-pairs-at1331 ∷ᵃ lem-pairs-at143143 ∷ᵃ lem-pairs-at2332 ∷ᵃ lem-pairs-at3443 ∷ᵃ lem-CSdu-box-3-at0314213042 ∷ᵃ lem-CXu-box-4-at0210243143 ∷ᵃ lem-box-perm-2341-at021021 ∷ᵃ lem-box-perm-4123-at02233440 ∷ᵃ lem-pairs-at0210233441 ∷ᵃ lem-pairs-at0210243143 ∷ᵃ lem-pairs-at022330 ∷ᵃ lem-pairs-at0312243140 ∷ᵃ lem-pairs-at243243 ∷ᵃ lem-pairs-at12233441 ∷ᵃ lem-pairs-at122441 ∷ᵃ lem-pairs-at14213243 ∷ᵃ nil
lem-F5-01 : _
lem-F5-01 = D025.lem-F5-01 sD025
lem-F5-23 : _
lem-F5-23 = D025.lem-F5-23 sD025
lem-box-perm-1423 : _
lem-box-perm-1423 = D025.lem-box-perm-1423 sD025
lem-box-perm-2431 : _
lem-box-perm-2431 = D025.lem-box-perm-2431 sD025
lem-box-perm-1243 : _
lem-box-perm-1243 = D025.lem-box-perm-1243 sD025
lem-box-perm-1342 : _
lem-box-perm-1342 = D025.lem-box-perm-1342 sD025
lem-box-perm-2341 : _
lem-box-perm-2341 = D025.lem-box-perm-2341 sD025
lem-CKu-box-1 : _
lem-CKu-box-1 = D025.lem-CKu-box-1 sD025
lem-CKdu-box-1 : _
lem-CKdu-box-1 = D025.lem-CKdu-box-1 sD025
lem-CKu-box-2 : _
lem-CKu-box-2 = D025.lem-CKu-box-2 sD025
lem-CKdu-box-2 : _
lem-CKdu-box-2 = D025.lem-CKdu-box-2 sD025
lem-CKu-box-3 : _
lem-CKu-box-3 = D025.lem-CKu-box-3 sD025
lem-CKdu-box-3 : _
lem-CKdu-box-3 = D025.lem-CKdu-box-3 sD025
lem-CKu-box-4 : _
lem-CKu-box-4 = D025.lem-CKu-box-4 sD025
lem-CKdu-box-4 : _
lem-CKdu-box-4 = D025.lem-CKdu-box-4 sD025
lem-box-perm-1243-at3443 : _
lem-box-perm-1243-at3443 = D025.lem-box-perm-1243-at3443 sD025
lem-F0-R : _
lem-F0-R = D025.lem-F0-R sD025
lem-box-perm-4312-at0330 : _
lem-box-perm-4312-at0330 = D025.lem-box-perm-4312-at0330 sD025
lem-box-perm-3421-at0314203142 : _
lem-box-perm-3421-at0314203142 = D025.lem-box-perm-3421-at0314203142 sD025
lem-CKdu-box-2-at243243 : _
lem-CKdu-box-2-at243243 = D025.lem-CKdu-box-2-at243243 sD025
lem-CKdu-box-2-at122441 : _
lem-CKdu-box-2-at122441 = D025.lem-CKdu-box-2-at122441 sD025
lem-box-perm-1423-at0210243143 : _
lem-box-perm-1423-at0210243143 = D025.lem-box-perm-1423-at0210243143 sD025
lem-F4-K1-CS2 : _
lem-F4-K1-CS2 = D025.lem-F4-K1-CS2 sD025
lem-CKdu-box-2-at0210243143 : _
lem-CKdu-box-2-at0210243143 = D025.lem-CKdu-box-2-at0210243143 sD025
lem-box-perm-1423-at243243 : _
lem-box-perm-1423-at243243 = D025.lem-box-perm-1423-at243243 sD025
lem-F4-K3-CS0 : _
lem-F4-K3-CS0 = D025.lem-F4-K3-CS0 sD025
lem-F4-K3-CS1 : _
lem-F4-K3-CS1 = D025.lem-F4-K3-CS1 sD025
lem-F4-K3-CS2 : _
lem-F4-K3-CS2 = D025.lem-F4-K3-CS2 sD025
lem-CKu-box-2-at0210243143 : _
lem-CKu-box-2-at0210243143 = D025.lem-CKu-box-2-at0210243143 sD025
lem-F4-CS0-K3 : _
lem-F4-CS0-K3 = D025.lem-F4-CS0-K3 sD025
lem-CKu-box-2-at243243 : _
lem-CKu-box-2-at243243 = D025.lem-CKu-box-2-at243243 sD025
lem-F4-CS1-K3 : _
lem-F4-CS1-K3 = D025.lem-F4-CS1-K3 sD025
lem-CKu-box-2-at122441 : _
lem-CKu-box-2-at122441 = D025.lem-CKu-box-2-at122441 sD025
lem-F4-CS2-K1 : _
lem-F4-CS2-K1 = D025.lem-F4-CS2-K1 sD025
lem-F4-CS2-K3 : _
lem-F4-CS2-K3 = D025.lem-F4-CS2-K3 sD025
lem-box-perm-4312-at0214213043 : _
lem-box-perm-4312-at0214213043 = D025.lem-box-perm-4312-at0214213043 sD025
lem-box-perm-3421-at0213203441 : _
lem-box-perm-3421-at0213203441 = D025.lem-box-perm-3421-at0213203441 sD025
lem-F0-R-at14213243 : _
lem-F0-R-at14213243 = D025.lem-F0-R-at14213243 sD025
lem-CXAu-S-at14213243 : _
lem-CXAu-S-at14213243 = D025.lem-CXAu-S-at14213243 sD025
lem-box-perm-1342-at0310243142 : _
lem-box-perm-1342-at0310243142 = D025.lem-box-perm-1342-at0310243142 sD025
lem-box-perm-4132-at243243 : _
lem-box-perm-4132-at243243 = D025.lem-box-perm-4132-at243243 sD025
lem-box-perm-4123-at033440 : _
lem-box-perm-4123-at033440 = D025.lem-box-perm-4123-at033440 sD025
lem-box-perm-2431-at132132 : _
lem-box-perm-2431-at132132 = D025.lem-box-perm-2431-at132132 sD025
lem-box-perm-1423-at03102132 : _
lem-box-perm-1423-at03102132 = D025.lem-box-perm-1423-at03102132 sD025
lem-box-perm-1342-at0210243143 : _
lem-box-perm-1342-at0210243143 = D025.lem-box-perm-1342-at0210243143 sD025
lem-box-box-1-at021021 : _
lem-box-box-1-at021021 = D025.lem-box-box-1-at021021 sD025
lem-box-perm-1432-at1221 : _
lem-box-perm-1432-at1221 = D025.lem-box-perm-1432-at1221 sD025
lem-box-perm-1423-at021021 : _
lem-box-perm-1423-at021021 = D025.lem-box-perm-1423-at021021 sD025
lem-box-perm-1342-at243243 : _
lem-box-perm-1342-at243243 = D025.lem-box-perm-1342-at243243 sD025
lem-box-perm-3241-at243243 : _
lem-box-perm-3241-at243243 = D025.lem-box-perm-3241-at243243 sD025
lem-box-perm-4213-at122441 : _
lem-box-perm-4213-at122441 = D025.lem-box-perm-4213-at122441 sD025
lem-box-perm-4132-at122441 : _
lem-box-perm-4132-at122441 = D025.lem-box-perm-4132-at122441 sD025
lem-F2-K1-CS2 : _
lem-F2-K1-CS2 = D025.lem-F2-K1-CS2 sD025
sD037 : SD037
sD037 = lem-box-tQ-at0214213043 ∷ᵃ lem-box-tQ-at0314213042 ∷ᵃ lem-box-tQ-at0330 ∷ᵃ lem-box-tQ-at033440 ∷ᵃ lem-box-tQ-at043043 ∷ᵃ lem-box-tQ-at12233441 ∷ᵃ lem-box-tQ-at233442 ∷ᵃ lem-box-tQ-at3443 ∷ᵃ lem-box-cP-at021021 ∷ᵃ lem-box-cP-at03102132 ∷ᵃ lem-box-cP-at04203243 ∷ᵃ lem-box-cP-at0110 ∷ᵃ lem-box-cP-at0210233441 ∷ᵃ lem-box-cP-at0210243143 ∷ᵃ lem-box-cP-at0314203142 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-cP-at132132 ∷ᵃ lem-box-cP-at233442 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-box-perm-2314-at0410213243 ∷ᵃ lem-Kdu-box ∷ᵃ lem-Ku-box ∷ᵃ lem-Ku-box-at0210243143 ∷ᵃ lem-Ku-box-at122441 ∷ᵃ lem-Ku-box-at243243 ∷ᵃ lem-box-box-4-at0410213243 ∷ᵃ lem-box-perm-1324-at043043 ∷ᵃ lem-box-perm-1423-at233442 ∷ᵃ lem-box-perm-3124-at043043 ∷ᵃ lem-box-perm-4123-at12233441 ∷ᵃ lem-box-box-4-at0310243142 ∷ᵃ lem-box-perm-1324-at0314213042 ∷ᵃ lem-box-perm-2314-at0310243142 ∷ᵃ lem-box-perm-2341-at03102132 ∷ᵃ lem-box-perm-3124-at0314213042 ∷ᵃ lem-CKdu-box-1 ∷ᵃ lem-CKdu-box-2 ∷ᵃ lem-CKdu-box-2-at0210243143 ∷ᵃ lem-CKdu-box-2-at122441 ∷ᵃ lem-CKdu-box-2-at243243 ∷ᵃ lem-CKdu-box-3 ∷ᵃ lem-CKdu-box-4 ∷ᵃ lem-CKu-box-1 ∷ᵃ lem-CKu-box-2 ∷ᵃ lem-CKu-box-2-at0210243143 ∷ᵃ lem-CKu-box-2-at122441 ∷ᵃ lem-CKu-box-2-at243243 ∷ᵃ lem-CKu-box-3 ∷ᵃ lem-CKu-box-4 ∷ᵃ lem-box-perm-1243 ∷ᵃ lem-box-perm-1243-at3443 ∷ᵃ lem-box-perm-1342 ∷ᵃ lem-box-perm-1423-at0210243143 ∷ᵃ lem-box-perm-1423-at243243 ∷ᵃ lem-box-perm-2341 ∷ᵃ lem-box-perm-3421-at0213203441 ∷ᵃ lem-box-perm-3421-at0314203142 ∷ᵃ lem-box-perm-4123-at033440 ∷ᵃ lem-box-perm-4312-at0214213043 ∷ᵃ lem-box-perm-4312-at0330 ∷ᵃ nil
lem-box-box-2 : _
lem-box-box-2 = D037.lem-box-box-2 sD037
lem-box-box-3 : _
lem-box-box-3 = D037.lem-box-box-3 sD037
lem-F0-B : _
lem-F0-B = D037.lem-F0-B sD037
lem-XCKX-box-2-at243243 : _
lem-XCKX-box-2-at243243 = D037.lem-XCKX-box-2-at243243 sD037
lem-XCKX-box-2-at122441 : _
lem-XCKX-box-2-at122441 = D037.lem-XCKX-box-2-at122441 sD037
lem-F4-K1-CS0 : _
lem-F4-K1-CS0 = D037.lem-F4-K1-CS0 sD037
lem-XCKX-box-2-at0210243143 : _
lem-XCKX-box-2-at0210243143 = D037.lem-XCKX-box-2-at0210243143 sD037
lem-F4-K2-CS1 : _
lem-F4-K2-CS1 = D037.lem-F4-K2-CS1 sD037
lem-F4-CS0-K1 : _
lem-F4-CS0-K1 = D037.lem-F4-CS0-K1 sD037
lem-F4-CS0-K2 : _
lem-F4-CS0-K2 = D037.lem-F4-CS0-K2 sD037
lem-F4-CS1-K0 : _
lem-F4-CS1-K0 = D037.lem-F4-CS1-K0 sD037
lem-F4-CS1-K2 : _
lem-F4-CS1-K2 = D037.lem-F4-CS1-K2 sD037
lem-F4-CS2-K0 : _
lem-F4-CS2-K0 = D037.lem-F4-CS2-K0 sD037
lem-F0-B-at14213243 : _
lem-F0-B-at14213243 = D037.lem-F0-B-at14213243 sD037
lem-box-box-1-at03102132 : _
lem-box-box-1-at03102132 = D037.lem-box-box-1-at03102132 sD037
sD017 : SD017
sD017 = lem-sym-ab-at0210243143 ∷ᵃ lem-sym-ab-at0310243142 ∷ᵃ lem-sym-ab-at032032 ∷ᵃ lem-sym-ab-at13243142 ∷ᵃ lem-sym-ab-at022330 ∷ᵃ lem-sym-ab-at0330 ∷ᵃ lem-nat-SWbc-at041041 ∷ᵃ lem-nat-SWbc-at0413203142 ∷ᵃ lem-nat-SWbc-at0413213042 ∷ᵃ lem-nat-SWbc-at04233240 ∷ᵃ lem-nat-SWbc-at0440 ∷ᵃ lem-sym-ab-at02102331 ∷ᵃ lem-sym-ab-at031031 ∷ᵃ lem-box-tQ-at03102132 ∷ᵃ lem-box-tQ-at032032 ∷ᵃ lem-box-tQ-at04203243 ∷ᵃ lem-box-tQ-at0310213442 ∷ᵃ lem-nat-SWbc-at02102331 ∷ᵃ lem-nat-SWbc-at04122041 ∷ᵃ lem-nat-SWbc-at04122140 ∷ᵃ lem-nat-SWbc-at0412233041 ∷ᵃ lem-nat-SWbc-at0412233140 ∷ᵃ lem-nat-SWbc-at0413213240 ∷ᵃ lem-nat-SWbc-at04133140 ∷ᵃ lem-nat-SWbc-at142142 ∷ᵃ lem-box-tQ-at0314203142 ∷ᵃ lem-t-cP-at03102132 ∷ᵃ lem-t-cP-at032032 ∷ᵃ lem-tP-at02102331 ∷ᵃ lem-tP-at02142041 ∷ᵃ lem-tP-at0314203241 ∷ᵃ lem-tP-at03243042 ∷ᵃ lem-tP-at04103143 ∷ᵃ lem-tP-at04122041 ∷ᵃ lem-tP-at0412233041 ∷ᵃ lem-tP-at04233042 ∷ᵃ lem-tP-at142142 ∷ᵃ lem-P-box-at0410213243 ∷ᵃ lem-P-box-at04203243 ∷ᵃ lem-box-tQ-at0412233041 ∷ᵃ lem-box-tQ-at0412233140 ∷ᵃ lem-t-cP-at0310213442 ∷ᵃ lem-t-cP-at04203243 ∷ᵃ lem-tP-at02142140 ∷ᵃ lem-tP-at0410233142 ∷ᵃ lem-tP-at0410233241 ∷ᵃ lem-tP-at0412213043 ∷ᵃ lem-tP-at04122140 ∷ᵃ lem-tP-at0412233140 ∷ᵃ lem-tP-at0413203142 ∷ᵃ lem-tP-at0413203241 ∷ᵃ lem-tP-at0413213240 ∷ᵃ lem-tP-at0440 ∷ᵃ lem-box-cP-at03102132 ∷ᵃ lem-box-cP-at032032 ∷ᵃ lem-box-cP-at0410213243 ∷ᵃ lem-box-cP-at04203243 ∷ᵃ lem-sym-bc-at0220 ∷ᵃ lem-sym-bc-at03102132 ∷ᵃ lem-sym-bc-at0310213442 ∷ᵃ lem-sym-bc-at032032 ∷ᵃ lem-sym-bc-at04203243 ∷ᵃ lem-sym-bc-at14233142 ∷ᵃ lem-QVQ-at02102331 ∷ᵃ lem-QVQ-at02142041 ∷ᵃ lem-QVQ-at02142140 ∷ᵃ lem-QVQ-at0314203241 ∷ᵃ lem-QVQ-at03243042 ∷ᵃ lem-QVQ-at0410233142 ∷ᵃ lem-QVQ-at0410233241 ∷ᵃ lem-QVQ-at04103143 ∷ᵃ lem-QVQ-at04122041 ∷ᵃ lem-QVQ-at0412213043 ∷ᵃ lem-QVQ-at04122140 ∷ᵃ lem-QVQ-at0412233041 ∷ᵃ lem-QVQ-at0412233140 ∷ᵃ lem-QVQ-at0413203142 ∷ᵃ lem-QVQ-at0413203241 ∷ᵃ lem-QVQ-at0413213240 ∷ᵃ lem-QVQ-at04233042 ∷ᵃ lem-QVQ-at0440 ∷ᵃ lem-QVQ-at142142 ∷ᵃ lem-SWbc-box-at02102331 ∷ᵃ lem-SWbc-box-at041041 ∷ᵃ lem-SWbc-box-at04122041 ∷ᵃ lem-SWbc-box-at04122140 ∷ᵃ lem-SWbc-box-at0412233041 ∷ᵃ lem-SWbc-box-at0412233140 ∷ᵃ lem-SWbc-box-at0413203142 ∷ᵃ lem-SWbc-box-at0413213042 ∷ᵃ lem-SWbc-box-at0413213240 ∷ᵃ lem-SWbc-box-at04133140 ∷ᵃ lem-SWbc-box-at04233240 ∷ᵃ lem-SWbc-box-at0440 ∷ᵃ lem-SWbc-box-at142142 ∷ᵃ lem-XCSX-box-2-at04122041 ∷ᵃ lem-box-cP-at0213243041 ∷ᵃ lem-box-cP-at0310213442 ∷ᵃ lem-sym-bc-at021021 ∷ᵃ lem-sym-bc-at0210213443 ∷ᵃ nil
lem-box-cP-at02142041 : _
lem-box-cP-at02142041 = D017.lem-box-cP-at02142041 sD017
lem-box-cP-at0314203241 : _
lem-box-cP-at0314203241 = D017.lem-box-cP-at0314203241 sD017
lem-box-perm-1324-at032032 : _
lem-box-perm-1324-at032032 = D017.lem-box-perm-1324-at032032 sD017
lem-box-perm-3124-at032032 : _
lem-box-perm-3124-at032032 = D017.lem-box-perm-3124-at032032 sD017
lem-box-perm-3124-at0220 : _
lem-box-perm-3124-at0220 = D017.lem-box-perm-3124-at0220 sD017
lem-sym-bc-at142142 : _
lem-sym-bc-at142142 = D017.lem-sym-bc-at142142 sD017
lem-box-perm-2314-at13243142 : _
lem-box-perm-2314-at13243142 = D017.lem-box-perm-2314-at13243142 sD017
lem-box-cP-at03243042 : _
lem-box-cP-at03243042 = D017.lem-box-cP-at03243042 sD017
lem-sym-bc-at02102331 : _
lem-sym-bc-at02102331 = D017.lem-sym-bc-at02102331 sD017
lem-box-cP-at142142 : _
lem-box-cP-at142142 = D017.lem-box-cP-at142142 sD017
lem-sym-bc-at04122041 : _
lem-sym-bc-at04122041 = D017.lem-sym-bc-at04122041 sD017
lem-box-cP-at0412233041 : _
lem-box-cP-at0412233041 = D017.lem-box-cP-at0412233041 sD017
lem-box-cP-at04122041 : _
lem-box-cP-at04122041 = D017.lem-box-cP-at04122041 sD017
lem-box-cP-at04103143 : _
lem-box-cP-at04103143 = D017.lem-box-cP-at04103143 sD017
lem-pairs-at0410213243 : _
lem-pairs-at0410213243 = D017.lem-pairs-at0410213243 sD017
lem-sym-bc-at0412233041 : _
lem-sym-bc-at0412233041 = D017.lem-sym-bc-at0412233041 sD017
lem-box-perm-1324-at04203243 : _
lem-box-perm-1324-at04203243 = D017.lem-box-perm-1324-at04203243 sD017
lem-box-cP-at0410233241 : _
lem-box-cP-at0410233241 = D017.lem-box-cP-at0410233241 sD017
lem-box-cP-at0440 : _
lem-box-cP-at0440 = D017.lem-box-cP-at0440 sD017
lem-box-cP-at0413203142 : _
lem-box-cP-at0413203142 = D017.lem-box-cP-at0413203142 sD017
lem-box-cP-at0413213240 : _
lem-box-cP-at0413213240 = D017.lem-box-cP-at0413213240 sD017
lem-CSdu-box-3-at0310213442 : _
lem-CSdu-box-3-at0310213442 = D017.lem-CSdu-box-3-at0310213442 sD017
sD021 : SD021
sD021 = lem-sym-ab-at0210243143 ∷ᵃ lem-sym-ab-at0214203143 ∷ᵃ lem-sym-ab-at03102132 ∷ᵃ lem-sym-ab-at0314203142 ∷ᵃ lem-sym-ab-at13243142 ∷ᵃ lem-sym-ab-at14233142 ∷ᵃ lem-sym-ab-at243243 ∷ᵃ lem-sym-ab-at0213243041 ∷ᵃ lem-sym-ab-at0214233041 ∷ᵃ lem-sym-ab-at03122031 ∷ᵃ lem-sym-ab-at03122130 ∷ᵃ lem-sym-ab-at0312243041 ∷ᵃ lem-sym-ab-at0314213240 ∷ᵃ lem-sym-ab-at03143041 ∷ᵃ lem-sym-ab-at03243240 ∷ᵃ lem-sym-ab-at14213243 ∷ᵃ lem-sym-ab-at02132031 ∷ᵃ lem-sym-ab-at02132130 ∷ᵃ lem-box-tQ-at03102132 ∷ᵃ lem-box-tQ-at14233241 ∷ᵃ lem-box-tQ-at0310213442 ∷ᵃ lem-box-tQ-at0214203143 ∷ᵃ lem-box-tQ-at0310243142 ∷ᵃ lem-box-tQ-at0314203142 ∷ᵃ lem-box-tQ-at0314213042 ∷ᵃ lem-box-tQ-at033440 ∷ᵃ lem-box-tQ-at13213442 ∷ᵃ lem-box-tQ-at1331 ∷ᵃ lem-box-tQ-at143143 ∷ᵃ lem-box-tQ-at02102441 ∷ᵃ lem-box-tQ-at02132130 ∷ᵃ lem-box-tQ-at02142041 ∷ᵃ lem-box-tQ-at02233440 ∷ᵃ lem-box-tQ-at0310243241 ∷ᵃ lem-box-tQ-at031031 ∷ᵃ lem-box-tQ-at03103441 ∷ᵃ lem-box-tQ-at03122031 ∷ᵃ lem-box-tQ-at0312203441 ∷ᵃ lem-box-tQ-at03122130 ∷ᵃ lem-box-tQ-at0314203241 ∷ᵃ lem-box-tQ-at0314213240 ∷ᵃ lem-box-tQ-at03143140 ∷ᵃ lem-box-tQ-at03243042 ∷ᵃ lem-box-tQ-at03243240 ∷ᵃ lem-box-tQ-at142142 ∷ᵃ lem-P-box-at0214203143 ∷ᵃ lem-P-box-at02233440 ∷ᵃ lem-P-box-at03103441 ∷ᵃ lem-P-box-at0312203441 ∷ᵃ lem-P-box-at0314203142 ∷ᵃ lem-P-box-at0314213042 ∷ᵃ lem-P-box-at0314213240 ∷ᵃ lem-P-box-at03243240 ∷ᵃ lem-P-box-at033440 ∷ᵃ lem-P-box-at12213443 ∷ᵃ lem-P-box-at1441 ∷ᵃ lem-P-box-at233442 ∷ᵃ lem-t-cP-at0310243142 ∷ᵃ lem-t-cP-at03143140 ∷ᵃ lem-t-cP-at03243240 ∷ᵃ lem-P-box-at02102441 ∷ᵃ lem-P-box-at02132130 ∷ᵃ lem-P-box-at0310243241 ∷ᵃ lem-P-box-at031031 ∷ᵃ lem-P-box-at03122130 ∷ᵃ lem-P-box-at0312243041 ∷ᵃ lem-P-box-at03143041 ∷ᵃ lem-P-box-at03243042 ∷ᵃ lem-P-box-at2442 ∷ᵃ lem-t-cP-at02142041 ∷ᵃ lem-t-cP-at0314203241 ∷ᵃ lem-t-cP-at033440 ∷ᵃ lem-t-cP-at142142 ∷ᵃ lem-sym-bc-at0210213443 ∷ᵃ lem-sym-bc-at0214233041 ∷ᵃ lem-box-cP-at0210243143 ∷ᵃ lem-box-cP-at02102441 ∷ᵃ lem-box-cP-at02132130 ∷ᵃ lem-box-cP-at0214203143 ∷ᵃ lem-box-cP-at02233440 ∷ᵃ lem-box-cP-at022440 ∷ᵃ lem-box-cP-at0310243142 ∷ᵃ lem-box-cP-at0310243241 ∷ᵃ lem-box-cP-at031031 ∷ᵃ lem-box-cP-at03103441 ∷ᵃ lem-box-cP-at0312203441 ∷ᵃ lem-box-cP-at03122130 ∷ᵃ lem-box-cP-at0312243041 ∷ᵃ lem-box-cP-at0314203142 ∷ᵃ lem-box-cP-at0314213042 ∷ᵃ lem-box-cP-at0314213240 ∷ᵃ lem-box-cP-at03143041 ∷ᵃ lem-box-cP-at03143140 ∷ᵃ lem-box-cP-at03243240 ∷ᵃ lem-box-cP-at033440 ∷ᵃ lem-box-cP-at12213443 ∷ᵃ lem-box-cP-at12243143 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-cP-at13213442 ∷ᵃ lem-box-cP-at1441 ∷ᵃ lem-box-cP-at233442 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-box-cP-at2442 ∷ᵃ lem-pairs-at021021 ∷ᵃ lem-pairs-at0210213443 ∷ᵃ lem-pairs-at0213243041 ∷ᵃ lem-pairs-at0214233041 ∷ᵃ lem-pairs-at03102132 ∷ᵃ lem-pairs-at0310213442 ∷ᵃ lem-pairs-at13243142 ∷ᵃ lem-pairs-at14233142 ∷ᵃ lem-sym-bc-at0210233441 ∷ᵃ lem-sym-bc-at0210243143 ∷ᵃ lem-sym-bc-at02102441 ∷ᵃ lem-sym-bc-at02142041 ∷ᵃ lem-sym-bc-at022330 ∷ᵃ lem-sym-bc-at02233440 ∷ᵃ lem-sym-bc-at022440 ∷ᵃ lem-sym-bc-at0310243142 ∷ᵃ lem-sym-bc-at0310243241 ∷ᵃ lem-sym-bc-at031031 ∷ᵃ lem-sym-bc-at03103441 ∷ᵃ lem-sym-bc-at0312203441 ∷ᵃ lem-sym-bc-at0312243041 ∷ᵃ lem-sym-bc-at0314203241 ∷ᵃ lem-sym-bc-at0314213240 ∷ᵃ lem-sym-bc-at03143041 ∷ᵃ lem-sym-bc-at03143140 ∷ᵃ lem-sym-bc-at03243240 ∷ᵃ lem-sym-bc-at0330 ∷ᵃ lem-sym-bc-at033440 ∷ᵃ lem-sym-bc-at12213443 ∷ᵃ lem-sym-bc-at12233441 ∷ᵃ lem-sym-bc-at12243143 ∷ᵃ lem-sym-bc-at13213442 ∷ᵃ lem-sym-bc-at14213243 ∷ᵃ lem-sym-bc-at143143 ∷ᵃ lem-sym-bc-at233442 ∷ᵃ lem-sym-bc-at2442 ∷ᵃ lem-sym-bc-at3443 ∷ᵃ lem-box-cP-at02142041 ∷ᵃ lem-box-cP-at0314203241 ∷ᵃ lem-box-cP-at03243042 ∷ᵃ lem-box-cP-at142142 ∷ᵃ lem-sym-bc-at02102331 ∷ᵃ lem-sym-bc-at142142 ∷ᵃ nil
lem-nf-comm-CS-S0at2 : _
lem-nf-comm-CS-S0at2 = D021.lem-nf-comm-CS-S0at2 sD021
lem-nf-comm-CS-S1at0 : _
lem-nf-comm-CS-S1at0 = D021.lem-nf-comm-CS-S1at0 sD021
lem-nf-comm-CS-S1at1 : _
lem-nf-comm-CS-S1at1 = D021.lem-nf-comm-CS-S1at1 sD021
lem-nf-comm-CS-S1at2 : _
lem-nf-comm-CS-S1at2 = D021.lem-nf-comm-CS-S1at2 sD021
lem-pairs-at0214203143 : _
lem-pairs-at0214203143 = D021.lem-pairs-at0214203143 sD021
lem-box-perm-1324-at02233440 : _
lem-box-perm-1324-at02233440 = D021.lem-box-perm-1324-at02233440 sD021
lem-Xb-box-at022440 : _
lem-Xb-box-at022440 = D021.lem-Xb-box-at022440 sD021
lem-box-perm-1324-at022440 : _
lem-box-perm-1324-at022440 = D021.lem-box-perm-1324-at022440 sD021
lem-pairs-at02233440 : _
lem-pairs-at02233440 = D021.lem-pairs-at02233440 sD021
lem-box-perm-1324-at12233441 : _
lem-box-perm-1324-at12233441 = D021.lem-box-perm-1324-at12233441 sD021
lem-pairs-at1441 : _
lem-pairs-at1441 = D021.lem-pairs-at1441 sD021
lem-box-perm-1324-at13213442 : _
lem-box-perm-1324-at13213442 = D021.lem-box-perm-1324-at13213442 sD021
lem-box-perm-1324-at0210233441 : _
lem-box-perm-1324-at0210233441 = D021.lem-box-perm-1324-at0210233441 sD021
lem-Xb-box-at02102441 : _
lem-Xb-box-at02102441 = D021.lem-Xb-box-at02102441 sD021
lem-box-perm-1324-at02102441 : _
lem-box-perm-1324-at02102441 = D021.lem-box-perm-1324-at02102441 sD021
lem-box-perm-1324-at233442 : _
lem-box-perm-1324-at233442 = D021.lem-box-perm-1324-at233442 sD021
lem-Xb-box-at2442 : _
lem-Xb-box-at2442 = D021.lem-Xb-box-at2442 sD021
lem-box-perm-1324-at2442 : _
lem-box-perm-1324-at2442 = D021.lem-box-perm-1324-at2442 sD021
lem-pairs-at233442 : _
lem-pairs-at233442 = D021.lem-pairs-at233442 sD021
lem-box-perm-1324-at12213443 : _
lem-box-perm-1324-at12213443 = D021.lem-box-perm-1324-at12213443 sD021
lem-Xb-box-at12243143 : _
lem-Xb-box-at12243143 = D021.lem-Xb-box-at12243143 sD021
lem-box-perm-1324-at12243143 : _
lem-box-perm-1324-at12243143 = D021.lem-box-perm-1324-at12243143 sD021
lem-pairs-at12213443 : _
lem-pairs-at12213443 = D021.lem-pairs-at12213443 sD021
lem-box-perm-2314-at243243 : _
lem-box-perm-2314-at243243 = D021.lem-box-perm-2314-at243243 sD021
lem-box-perm-1324-at03143140 : _
lem-box-perm-1324-at03143140 = D021.lem-box-perm-1324-at03143140 sD021
lem-box-perm-3124-at03143140 : _
lem-box-perm-3124-at03143140 = D021.lem-box-perm-3124-at03143140 sD021
lem-box-box-4-at03243240 : _
lem-box-box-4-at03243240 = D021.lem-box-box-4-at03243240 sD021
lem-box-perm-2314-at03243240 : _
lem-box-perm-2314-at03243240 = D021.lem-box-perm-2314-at03243240 sD021
lem-CSdu-box-3-at03143140 : _
lem-CSdu-box-3-at03143140 = D021.lem-CSdu-box-3-at03143140 sD021
lem-CSu-box-3-at03143140 : _
lem-CSu-box-3-at03143140 = D021.lem-CSu-box-3-at03143140 sD021
lem-box2-at03143140 : _
lem-box2-at03143140 = D021.lem-box2-at03143140 sD021
lem-box-perm-3124-at143143 : _
lem-box-perm-3124-at143143 = D021.lem-box-perm-3124-at143143 sD021
lem-CXu-box-4-at243243 : _
lem-CXu-box-4-at243243 = D021.lem-CXu-box-4-at243243 sD021
lem-pairs-at0314203142 : _
lem-pairs-at0314203142 = D021.lem-pairs-at0314203142 sD021
lem-box2-at03243240 : _
lem-box2-at03243240 = D021.lem-box2-at03243240 sD021
lem-box-perm-1324-at03243240 : _
lem-box-perm-1324-at03243240 = D021.lem-box-perm-1324-at03243240 sD021
lem-pairs-at033440 : _
lem-pairs-at033440 = D021.lem-pairs-at033440 sD021
lem-box2-at0310243142 : _
lem-box2-at0310243142 = D021.lem-box2-at0310243142 sD021
lem-pairs-at0314213042 : _
lem-pairs-at0314213042 = D021.lem-pairs-at0314213042 sD021
lem-box-perm-1324-at03103441 : _
lem-box-perm-1324-at03103441 = D021.lem-box-perm-1324-at03103441 sD021
lem-Xb-box-at0310243241 : _
lem-Xb-box-at0310243241 = D021.lem-Xb-box-at0310243241 sD021
lem-box-perm-1324-at0310243241 : _
lem-box-perm-1324-at0310243241 = D021.lem-box-perm-1324-at0310243241 sD021
lem-pairs-at03103441 : _
lem-pairs-at03103441 = D021.lem-pairs-at03103441 sD021
lem-box-perm-1324-at0310243142 : _
lem-box-perm-1324-at0310243142 = D021.lem-box-perm-1324-at0310243142 sD021
lem-Xb-box-at0310243142 : _
lem-Xb-box-at0310243142 = D021.lem-Xb-box-at0310243142 sD021
lem-pairs-at0314213240 : _
lem-pairs-at0314213240 = D021.lem-pairs-at0314213240 sD021
lem-box-perm-1324-at0312203441 : _
lem-box-perm-1324-at0312203441 = D021.lem-box-perm-1324-at0312203441 sD021
lem-Xb-box-at0312243041 : _
lem-Xb-box-at0312243041 = D021.lem-Xb-box-at0312243041 sD021
lem-box-perm-1324-at0312243041 : _
lem-box-perm-1324-at0312243041 = D021.lem-box-perm-1324-at0312243041 sD021
lem-pairs-at0312203441 : _
lem-pairs-at0312203441 = D021.lem-pairs-at0312203441 sD021
lem-box-perm-1324-at033440 : _
lem-box-perm-1324-at033440 = D021.lem-box-perm-1324-at033440 sD021
lem-Xb-box-at03243240 : _
lem-Xb-box-at03243240 = D021.lem-Xb-box-at03243240 sD021
lem-box-perm-1324-at3443 : _
lem-box-perm-1324-at3443 = D021.lem-box-perm-1324-at3443 sD021
lem-pairs-at03243240 : _
lem-pairs-at03243240 = D021.lem-pairs-at03243240 sD021
lem-box-perm-1324-at02142041 : _
lem-box-perm-1324-at02142041 = D021.lem-box-perm-1324-at02142041 sD021
lem-box-perm-3124-at02142041 : _
lem-box-perm-3124-at02142041 = D021.lem-box-perm-3124-at02142041 sD021
lem-box-perm-3124-at0314203241 : _
lem-box-perm-3124-at0314203241 = D021.lem-box-perm-3124-at0314203241 sD021
lem-box-perm-2341-at0213243041 : _
lem-box-perm-2341-at0213243041 = D021.lem-box-perm-2341-at0213243041 sD021
lem-box-perm-4123-at0214203143 : _
lem-box-perm-4123-at0214203143 = D021.lem-box-perm-4123-at0214203143 sD021
lem-box-perm-2314-at0312243041 : _
lem-box-perm-2314-at0312243041 = D021.lem-box-perm-2314-at0312243041 sD021
lem-pairs-at0312243041 : _
lem-pairs-at0312243041 = D021.lem-pairs-at0312243041 sD021
lem-pairs-at02102441 : _
lem-pairs-at02102441 = D021.lem-pairs-at02102441 sD021
lem-pairs-at03143041 : _
lem-pairs-at03143041 = D021.lem-pairs-at03143041 sD021
lem-pairs-at02132130 : _
lem-pairs-at02132130 = D021.lem-pairs-at02132130 sD021
lem-box-perm-1324-at0314203241 : _
lem-box-perm-1324-at0314203241 = D021.lem-box-perm-1324-at0314203241 sD021
lem-box-perm-4123-at0314203142 : _
lem-box-perm-4123-at0314203142 = D021.lem-box-perm-4123-at0314203142 sD021
lem-pairs-at0310243241 : _
lem-pairs-at0310243241 = D021.lem-pairs-at0310243241 sD021
lem-box-perm-1243-at021021 : _
lem-box-perm-1243-at021021 = D021.lem-box-perm-1243-at021021 sD021
lem-box-perm-1243-at0210213443 : _
lem-box-perm-1243-at0210213443 = D021.lem-box-perm-1243-at0210213443 sD021
lem-pairs-at03122130 : _
lem-pairs-at03122130 = D021.lem-pairs-at03122130 sD021
lem-box-perm-2314-at02132130 : _
lem-box-perm-2314-at02132130 = D021.lem-box-perm-2314-at02132130 sD021
lem-box-perm-2314-at03122130 : _
lem-box-perm-2314-at03122130 = D021.lem-box-perm-2314-at03122130 sD021
lem-pairs-at031031 : _
lem-pairs-at031031 = D021.lem-pairs-at031031 sD021
lem-box-perm-1324-at142142 : _
lem-box-perm-1324-at142142 = D021.lem-box-perm-1324-at142142 sD021
lem-box-perm-3124-at142142 : _
lem-box-perm-3124-at142142 = D021.lem-box-perm-3124-at142142 sD021
lem-box-perm-2341-at13243142 : _
lem-box-perm-2341-at13243142 = D021.lem-box-perm-2341-at13243142 sD021
lem-pairs-at03243042 : _
lem-pairs-at03243042 = D021.lem-pairs-at03243042 sD021
lem-pairs-at2442 : _
lem-pairs-at2442 = D021.lem-pairs-at2442 sD021
sD026 : SD026
sD026 = lem-box-tQ-at0210213443 ∷ᵃ lem-box-tQ ∷ᵃ lem-box-tQ-at3443 ∷ᵃ lem-box-cP-at0210243143 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-box-perm-1324 ∷ᵃ lem-box-perm-1324-at0210243143 ∷ᵃ lem-box-perm-1324-at243243 ∷ᵃ lem-box2-at0210243143 ∷ᵃ lem-box2-at122441 ∷ᵃ lem-box2-at243243 ∷ᵃ lem-CSu-box-4-at122441 ∷ᵃ lem-Xb-box-at2332 ∷ᵃ lem-box-perm-1324-at2332 ∷ᵃ lem-nf-comm-CS-S0at0 ∷ᵃ lem-nf-comm-CS-S0at1 ∷ᵃ lem-nf-comm-CS-S0at2 ∷ᵃ lem-nf-comm-CS-S1at0 ∷ᵃ lem-nf-comm-CS-S1at1 ∷ᵃ nil
lem-F2-K3-CS0 : _
lem-F2-K3-CS0 = D026.lem-F2-K3-CS0 sD026
lem-F2-K3-CS1 : _
lem-F2-K3-CS1 = D026.lem-F2-K3-CS1 sD026
lem-AX-S23 : _
lem-AX-S23 = D026.lem-AX-S23 sD026
lem-CKc-box : _
lem-CKc-box = D026.lem-CKc-box sD026
lem-CKdc-box : _
lem-CKdc-box = D026.lem-CKdc-box sD026
lem-S2-SBOX⟨2·0·41·3⟩ : _
lem-S2-SBOX⟨2·0·41·3⟩ = D026.lem-S2-SBOX⟨2·0·41·3⟩ sD026
lem-S2-SBOX⟨0·1·42·3⟩ : _
lem-S2-SBOX⟨0·1·42·3⟩ = D026.lem-S2-SBOX⟨0·1·42·3⟩ sD026
lem-S2-SBOX⟨0·2·43·1⟩ : _
lem-S2-SBOX⟨0·2·43·1⟩ = D026.lem-S2-SBOX⟨0·2·43·1⟩ sD026
lem-F1-comm-CS-S0at2 : _
lem-F1-comm-CS-S0at2 = D026.lem-F1-comm-CS-S0at2 sD026
sD038 : SD038
sD038 = lem-nf-order-CSat0 ∷ᵃ lem-nf-order-CSat1 ∷ᵃ lem-nf-order-CSat2 ∷ᵃ lem-box-cP-at0210243143 ∷ᵃ lem-box-cP-at12233441 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-box-perm-1324-at122441 ∷ᵃ lem-box2 ∷ᵃ lem-CSdu-box-3-at0210243143 ∷ᵃ lem-CSdu-box-3-at122441 ∷ᵃ lem-CSu-box-3-at0210243143 ∷ᵃ lem-CSu-box-3-at122441 ∷ᵃ lem-box-perm-1432-at122441 ∷ᵃ lem-CKu-box-2-at0210243143 ∷ᵃ lem-CKu-box-2-at122441 ∷ᵃ lem-CKu-box-2-at243243 ∷ᵃ lem-box-box-1-at021021 ∷ᵃ lem-box-perm-1342-at0210243143 ∷ᵃ lem-box-perm-1423-at021021 ∷ᵃ lem-box-perm-1432-at1221 ∷ᵃ lem-box-perm-3241-at243243 ∷ᵃ lem-box-perm-4213-at122441 ∷ᵃ lem-CKc-box ∷ᵃ lem-CKdc-box ∷ᵃ lem-S2-SBOX⟨0·1·42·3⟩ ∷ᵃ lem-S2-SBOX⟨0·2·43·1⟩ ∷ᵃ lem-S2-SBOX⟨2·0·41·3⟩ ∷ᵃ nil
lem-F4-CS0-CS2 : _
lem-F4-CS0-CS2 = D038.lem-F4-CS0-CS2 sD038
lem-F4-CS1-CS2 : _
lem-F4-CS1-CS2 = D038.lem-F4-CS1-CS2 sD038
lem-F4-CS2-CS1 : _
lem-F4-CS2-CS1 = D038.lem-F4-CS2-CS1 sD038
lem-F2-K0-CS1 : _
lem-F2-K0-CS1 = D038.lem-F2-K0-CS1 sD038
lem-F2-K0-CS2 : _
lem-F2-K0-CS2 = D038.lem-F2-K0-CS2 sD038
lem-F2-K2-CS0 : _
lem-F2-K2-CS0 = D038.lem-F2-K2-CS0 sD038
lem-F1-order-CSat2 : _
lem-F1-order-CSat2 = D038.lem-F1-order-CSat2 sD038
sD027 : SD027
sD027 = lem-sym-ab-at0210243143 ∷ᵃ lem-sym-ab-at0214203143 ∷ᵃ lem-sym-ab-at0310243142 ∷ᵃ lem-sym-ab-at0314203142 ∷ᵃ lem-sym-ab-at122441 ∷ᵃ lem-sym-ab-at13213442 ∷ᵃ lem-sym-ab-at233442 ∷ᵃ lem-sym-ab-at243243 ∷ᵃ lem-sym-ab-at0314213240 ∷ᵃ lem-sym-ab-at03243240 ∷ᵃ lem-sym-ab-at14213243 ∷ᵃ lem-sym-ab-at1441 ∷ᵃ lem-box-tQ-at0310213442 ∷ᵃ lem-box-tQ-at0210233441 ∷ᵃ lem-box-tQ-at033440 ∷ᵃ lem-box-tQ-at12213443 ∷ᵃ lem-box-tQ-at12233441 ∷ᵃ lem-box-tQ-at13213442 ∷ᵃ lem-box-tQ-at233442 ∷ᵃ lem-box-tQ-at02233440 ∷ᵃ lem-box-tQ-at03103441 ∷ᵃ lem-box-tQ-at0312203441 ∷ᵃ lem-box-tQ-at03143140 ∷ᵃ lem-sym-bc-at14233241 ∷ᵃ lem-Xb-box-at13243142 ∷ᵃ lem-box-cP-at0310243142 ∷ᵃ lem-box-cP-at03243240 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-perm-1324-at0310213442 ∷ᵃ lem-box-perm-1324-at13243142 ∷ᵃ lem-sym-bc-at0214213043 ∷ᵃ lem-sym-bc-at0314203142 ∷ᵃ lem-sym-bc-at0314213042 ∷ᵃ lem-sym-bc-at03243240 ∷ᵃ lem-sym-bc-at033440 ∷ᵃ lem-sym-bc-at143143 ∷ᵃ lem-Xb-box-at122441 ∷ᵃ lem-box-perm-1324-at122441 ∷ᵃ lem-pairs-at13213442 ∷ᵃ lem-pairs-at143143 ∷ᵃ lem-pairs-at0210233441 ∷ᵃ lem-pairs-at12233441 ∷ᵃ lem-pairs-at14213243 ∷ᵃ lem-CSdu-box-3-at03143140 ∷ᵃ lem-CXu-box-4-at243243 ∷ᵃ lem-Xb-box-at02102441 ∷ᵃ lem-Xb-box-at022440 ∷ᵃ lem-Xb-box-at0310243142 ∷ᵃ lem-Xb-box-at0310243241 ∷ᵃ lem-Xb-box-at0312243041 ∷ᵃ lem-Xb-box-at03243240 ∷ᵃ lem-Xb-box-at12243143 ∷ᵃ lem-Xb-box-at2442 ∷ᵃ lem-box-perm-1324-at0210233441 ∷ᵃ lem-box-perm-1324-at02102441 ∷ᵃ lem-box-perm-1324-at02233440 ∷ᵃ lem-box-perm-1324-at022440 ∷ᵃ lem-box-perm-1324-at0310243142 ∷ᵃ lem-box-perm-1324-at0310243241 ∷ᵃ lem-box-perm-1324-at03103441 ∷ᵃ lem-box-perm-1324-at0312203441 ∷ᵃ lem-box-perm-1324-at0312243041 ∷ᵃ lem-box-perm-1324-at03243240 ∷ᵃ lem-box-perm-1324-at033440 ∷ᵃ lem-box-perm-1324-at12213443 ∷ᵃ lem-box-perm-1324-at12233441 ∷ᵃ lem-box-perm-1324-at12243143 ∷ᵃ lem-box-perm-1324-at13213442 ∷ᵃ lem-box-perm-1324-at233442 ∷ᵃ lem-box-perm-1324-at2442 ∷ᵃ lem-box2-at0310243142 ∷ᵃ lem-box2-at03243240 ∷ᵃ lem-nf-comm-CS-S1at2 ∷ᵃ lem-pairs-at0214203143 ∷ᵃ lem-pairs-at02233440 ∷ᵃ lem-pairs-at03103441 ∷ᵃ lem-pairs-at0312203441 ∷ᵃ lem-pairs-at0314203142 ∷ᵃ lem-pairs-at0314213042 ∷ᵃ lem-pairs-at0314213240 ∷ᵃ lem-pairs-at033440 ∷ᵃ lem-pairs-at12213443 ∷ᵃ lem-pairs-at1441 ∷ᵃ lem-pairs-at233442 ∷ᵃ nil
lem-F1-comm-CS-S1at2 : _
lem-F1-comm-CS-S1at2 = D027.lem-F1-comm-CS-S1at2 sD027
lem-box-perm-3421-at0210243143 : _
lem-box-perm-3421-at0210243143 = D027.lem-box-perm-3421-at0210243143 sD027
lem-CKc-box-at02233440 : _
lem-CKc-box-at02233440 = D027.lem-CKc-box-at02233440 sD027
lem-box-perm-4312-at02233440 : _
lem-box-perm-4312-at02233440 = D027.lem-box-perm-4312-at02233440 sD027
lem-box-perm-3421-at243243 : _
lem-box-perm-3421-at243243 = D027.lem-box-perm-3421-at243243 sD027
lem-CKc-box-at12233441 : _
lem-CKc-box-at12233441 = D027.lem-CKc-box-at12233441 sD027
lem-box-perm-4312-at12233441 : _
lem-box-perm-4312-at12233441 = D027.lem-box-perm-4312-at12233441 sD027
lem-box-perm-3421-at122441 : _
lem-box-perm-3421-at122441 = D027.lem-box-perm-3421-at122441 sD027
lem-CKc-box-at13213442 : _
lem-CKc-box-at13213442 = D027.lem-CKc-box-at13213442 sD027
lem-box-perm-4312-at13213442 : _
lem-box-perm-4312-at13213442 = D027.lem-box-perm-4312-at13213442 sD027
lem-CKc-box-at0210233441 : _
lem-CKc-box-at0210233441 = D027.lem-CKc-box-at0210233441 sD027
lem-box-perm-1342-at0210233441 : _
lem-box-perm-1342-at0210233441 = D027.lem-box-perm-1342-at0210233441 sD027
lem-CKc-box-at233442 : _
lem-CKc-box-at233442 = D027.lem-CKc-box-at233442 sD027
lem-box-perm-1342-at233442 : _
lem-box-perm-1342-at233442 = D027.lem-box-perm-1342-at233442 sD027
lem-CKc-box-at12213443 : _
lem-CKc-box-at12213443 = D027.lem-CKc-box-at12213443 sD027
lem-box-perm-1342-at12213443 : _
lem-box-perm-1342-at12213443 = D027.lem-box-perm-1342-at12213443 sD027
lem-box-perm-4312-at143143 : _
lem-box-perm-4312-at143143 = D027.lem-box-perm-4312-at143143 sD027
lem-box-perm-3421-at13213442 : _
lem-box-perm-3421-at13213442 = D027.lem-box-perm-3421-at13213442 sD027
lem-F0-R-at01143043 : _
lem-F0-R-at01143043 = D027.lem-F0-R-at01143043 sD027
lem-CXAu-S-at01143043 : _
lem-CXAu-S-at01143043 = D027.lem-CXAu-S-at01143043 sD027
lem-box-perm-3241-at0310243142 : _
lem-box-perm-3241-at0310243142 = D027.lem-box-perm-3241-at0310243142 sD027
lem-box-perm-4213-at03243240 : _
lem-box-perm-4213-at03243240 = D027.lem-box-perm-4213-at03243240 sD027
sD039 : SD039
sD039 = lem-box-tQ-at143143 ∷ᵃ lem-box-tQ-at03143140 ∷ᵃ lem-box-cP-at0210243143 ∷ᵃ lem-box-cP-at0314213240 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-box-perm-1423-at122441 ∷ᵃ lem-box-box-4-at03243240 ∷ᵃ lem-box-perm-1324-at03143140 ∷ᵃ lem-box-perm-2314-at03243240 ∷ᵃ lem-box-perm-3124-at03143140 ∷ᵃ lem-box-perm-1423-at0210243143 ∷ᵃ lem-box-perm-1423-at243243 ∷ᵃ lem-S2-SBOX⟨0·1·42·3⟩ ∷ᵃ lem-S2-SBOX⟨0·2·43·1⟩ ∷ᵃ lem-S2-SBOX⟨2·0·41·3⟩ ∷ᵃ lem-CKc-box-at0210233441 ∷ᵃ lem-CKc-box-at02233440 ∷ᵃ lem-CKc-box-at12213443 ∷ᵃ lem-CKc-box-at12233441 ∷ᵃ lem-CKc-box-at13213442 ∷ᵃ lem-CKc-box-at233442 ∷ᵃ lem-box-perm-1342-at0210233441 ∷ᵃ lem-box-perm-1342-at12213443 ∷ᵃ lem-box-perm-1342-at233442 ∷ᵃ lem-box-perm-3421-at0210243143 ∷ᵃ lem-box-perm-3421-at122441 ∷ᵃ lem-box-perm-3421-at13213442 ∷ᵃ lem-box-perm-3421-at243243 ∷ᵃ lem-box-perm-4312-at02233440 ∷ᵃ lem-box-perm-4312-at12233441 ∷ᵃ lem-box-perm-4312-at13213442 ∷ᵃ lem-box-perm-4312-at143143 ∷ᵃ nil
lem-nf-X-CS0at0 : _
lem-nf-X-CS0at0 = D039.lem-nf-X-CS0at0 sD039
lem-nf-X-CS0at1 : _
lem-nf-X-CS0at1 = D039.lem-nf-X-CS0at1 sD039
lem-nf-X-CS0at2 : _
lem-nf-X-CS0at2 = D039.lem-nf-X-CS0at2 sD039
lem-nf-X-CS1at0 : _
lem-nf-X-CS1at0 = D039.lem-nf-X-CS1at0 sD039
lem-nf-X-CS1at1 : _
lem-nf-X-CS1at1 = D039.lem-nf-X-CS1at1 sD039
lem-nf-X-CS1at2 : _
lem-nf-X-CS1at2 = D039.lem-nf-X-CS1at2 sD039
lem-F0-B-at01143043 : _
lem-F0-B-at01143043 = D039.lem-F0-B-at01143043 sD039
sD067 : SD067
sD067 = lem-inv-SBOX⟨2·0·41·3⟩ ∷ᵃ lem-invr-SBOX⟨2·0·41·3⟩ ∷ᵃ lem-box-tQ ∷ᵃ lem-box-tQ-at0330 ∷ᵃ lem-box-cP-at032032 ∷ᵃ lem-box-cP-at04203243 ∷ᵃ lem-box-cP-at0210243143 ∷ᵃ lem-box-cP-at0314203142 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-box-perm-2314-at03102132 ∷ᵃ lem-CSdu-box-3-at043043 ∷ᵃ lem-CSu-box-3-at043043 ∷ᵃ lem-box-perm-1324-at043043 ∷ᵃ lem-box-perm-3124 ∷ᵃ lem-box-perm-3124-at0330 ∷ᵃ lem-box2-at043043 ∷ᵃ lem-CSdu-box-3-at0210243143 ∷ᵃ lem-CSdu-box-3-at0314213042 ∷ᵃ lem-CSdu-box-3-at122441 ∷ᵃ lem-CSu-box-3-at0210243143 ∷ᵃ lem-CSu-box-3-at0314213042 ∷ᵃ lem-CSu-box-3-at122441 ∷ᵃ lem-box-perm-1324-at0314213042 ∷ᵃ lem-box-perm-2314-at0210243143 ∷ᵃ lem-box-perm-3124-at0214213043 ∷ᵃ lem-box2-at0314213042 ∷ᵃ lem-box-perm-1324-at0330 ∷ᵃ lem-box-perm-2314-at132132 ∷ᵃ lem-F0-R ∷ᵃ lem-F0-R-at14213243 ∷ᵃ lem-F5-01 ∷ᵃ lem-box-perm-1342-at0210243143 ∷ᵃ lem-box-perm-1423-at021021 ∷ᵃ lem-box-perm-2431 ∷ᵃ lem-box-perm-4132-at122441 ∷ᵃ lem-AX-S23 ∷ᵃ lem-F0-B ∷ᵃ lem-F0-B-at14213243 ∷ᵃ lem-XCKX-box-2-at0210243143 ∷ᵃ lem-XCKX-box-2-at122441 ∷ᵃ lem-XCKX-box-2-at243243 ∷ᵃ lem-box-box-1-at03102132 ∷ᵃ lem-box-box-2 ∷ᵃ lem-F4-CS0-CS2 ∷ᵃ lem-nf-X-CS0at0 ∷ᵃ lem-nf-X-CS0at1 ∷ᵃ lem-nf-X-CS0at2 ∷ᵃ lem-nf-X-CS1at0 ∷ᵃ lem-nf-X-CS1at1 ∷ᵃ nil
lem-CXuA-S : _
lem-CXuA-S = D067.lem-CXuA-S sD067
lem-F4-K0-CS1 : _
lem-F4-K0-CS1 = D067.lem-F4-K0-CS1 sD067
lem-F4-K0-CS2 : _
lem-F4-K0-CS2 = D067.lem-F4-K0-CS2 sD067
lem-F4-K2-CS0 : _
lem-F4-K2-CS0 = D067.lem-F4-K2-CS0 sD067
lem-CXuA-S-at14213243 : _
lem-CXuA-S-at14213243 = D067.lem-CXuA-S-at14213243 sD067
lem-F4-CS2-CS0 : _
lem-F4-CS2-CS0 = D067.lem-F4-CS2-CS0 sD067
lem-F2-CS0-CS2 : _
lem-F2-CS0-CS2 = D067.lem-F2-CS0-CS2 sD067
lem-F1-X-CS0at2 : _
lem-F1-X-CS0at2 = D067.lem-F1-X-CS0at2 sD067
sD028 : SD028
sD028 = lem-sym-ab-at03122031 ∷ᵃ lem-box-tQ-at3443 ∷ᵃ lem-sym-bc-at031031 ∷ᵃ lem-Xb-box-at243243 ∷ᵃ lem-box-perm-1324-at243243 ∷ᵃ lem-box-perm-1324-at3443 ∷ᵃ lem-pairs-at03243240 ∷ᵃ nil
lem-CKc-box-at3443 : _
lem-CKc-box-at3443 = D028.lem-CKc-box-at3443 sD028
lem-box-perm-4132-at03243240 : _
lem-box-perm-4132-at03243240 = D028.lem-box-perm-4132-at03243240 sD028
sD040 : SD040
sD040 = lem-box-cP-at122441 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-box-perm-1324-at243243 ∷ᵃ lem-box2-at122441 ∷ᵃ lem-box-perm-1324-at3443 ∷ᵃ lem-box-perm-1423-at243243 ∷ᵃ lem-box-perm-3241-at243243 ∷ᵃ lem-S2-SBOX⟨0·1·42·3⟩ ∷ᵃ lem-S2-SBOX⟨0·2·43·1⟩ ∷ᵃ lem-CKc-box-at233442 ∷ᵃ lem-box-perm-1342-at233442 ∷ᵃ lem-CKc-box-at3443 ∷ᵃ nil
lem-nf-comm-CSu-CSat1 : _
lem-nf-comm-CSu-CSat1 = D040.lem-nf-comm-CSu-CSat1 sD040
lem-nf-rel-266at1 : _
lem-nf-rel-266at1 = D040.lem-nf-rel-266at1 sD040
lem-nf-rel-267at1 : _
lem-nf-rel-267at1 = D040.lem-nf-rel-267at1 sD040
sD068 : SD068
sD068 = lem-box-cP-at0314213240 ∷ᵃ lem-box-cP-at12233441 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-box-perm-1324-at122441 ∷ᵃ lem-box2-at243243 ∷ᵃ lem-CSdu-box-3-at03143140 ∷ᵃ lem-CSu-box-3-at03143140 ∷ᵃ lem-box-perm-1324-at03143140 ∷ᵃ lem-box-perm-1324-at12233441 ∷ᵃ lem-box-perm-2314-at243243 ∷ᵃ lem-box-perm-3124-at143143 ∷ᵃ lem-box2-at03143140 ∷ᵃ lem-box-perm-4213-at122441 ∷ᵃ lem-S2-SBOX⟨0·1·42·3⟩ ∷ᵃ lem-S2-SBOX⟨0·2·43·1⟩ ∷ᵃ lem-CKc-box-at12233441 ∷ᵃ lem-CKc-box-at13213442 ∷ᵃ lem-F0-R-at01143043 ∷ᵃ lem-box-perm-3421-at122441 ∷ᵃ lem-box-perm-4312-at13213442 ∷ᵃ lem-F0-B-at01143043 ∷ᵃ lem-nf-X-CS1at2 ∷ᵃ lem-nf-comm-CSu-CSat1 ∷ᵃ lem-nf-rel-266at1 ∷ᵃ lem-nf-rel-267at1 ∷ᵃ nil
lem-F1-X-CS1at2 : _
lem-F1-X-CS1at2 = D068.lem-F1-X-CS1at2 sD068
lem-CXuA-S-at01143043 : _
lem-CXuA-S-at01143043 = D068.lem-CXuA-S-at01143043 sD068
sD042 : SD042
sD042 = lem-box-cP-at122441 ∷ᵃ lem-box-perm-1423-at122441 ∷ᵃ lem-box2-at122441 ∷ᵃ lem-S2-SBOX⟨0·1·42·3⟩ ∷ᵃ lem-S2-SBOX⟨2·0·41·3⟩ ∷ᵃ lem-CKc-box-at12213443 ∷ᵃ lem-CKc-box-at13213442 ∷ᵃ lem-box-perm-1342-at12213443 ∷ᵃ lem-box-perm-3421-at122441 ∷ᵃ lem-box-perm-4312-at13213442 ∷ᵃ nil
lem-nf-CS-K0at2 : _
lem-nf-CS-K0at2 = D042.lem-nf-CS-K0at2 sD042
lem-nf-CS-K1at2 : _
lem-nf-CS-K1at2 = D042.lem-nf-CS-K1at2 sD042
lem-L-CX01-1 : _
lem-L-CX01-1 = D042.lem-L-CX01-1 sD042
sD030 : SD030
sD030 = lem-sym-ab-at0310243142 ∷ᵃ lem-sym-ab-at02102441 ∷ᵃ lem-sym-ab-at02142041 ∷ᵃ lem-sym-ab-at0310243241 ∷ᵃ lem-sym-ab-at0312243041 ∷ᵃ lem-sym-ab-at0314203241 ∷ᵃ lem-sym-ab-at03143041 ∷ᵃ lem-box-tQ-at0210213443 ∷ᵃ lem-box-tQ-at0214203143 ∷ᵃ lem-sym-bc-at0310213442 ∷ᵃ lem-box-cP-at03122031 ∷ᵃ lem-box-cP-at0312243041 ∷ᵃ lem-pairs-at03102132 ∷ᵃ lem-pairs-at0310213442 ∷ᵃ lem-sym-bc-at02132031 ∷ᵃ lem-sym-bc-at02132130 ∷ᵃ lem-sym-bc-at03122031 ∷ᵃ lem-sym-bc-at03122130 ∷ᵃ lem-sym-bc-at0314203241 ∷ᵃ lem-box-perm-1243-at021021 ∷ᵃ lem-box-perm-1243-at0210213443 ∷ᵃ lem-box-perm-2341-at0213243041 ∷ᵃ lem-box-perm-4123-at0214203143 ∷ᵃ lem-pairs-at02102441 ∷ᵃ lem-pairs-at02132130 ∷ᵃ lem-pairs-at0310243241 ∷ᵃ lem-pairs-at03122130 ∷ᵃ lem-pairs-at0312243041 ∷ᵃ lem-pairs-at03143041 ∷ᵃ nil
lem-box-box-1-at0213243041 : _
lem-box-box-1-at0213243041 = D030.lem-box-box-1-at0213243041 sD030
lem-box-perm-1243-at03102132 : _
lem-box-perm-1243-at03102132 = D030.lem-box-perm-1243-at03102132 sD030
lem-box-perm-1243-at0310213442 : _
lem-box-perm-1243-at0310213442 = D030.lem-box-perm-1243-at0310213442 sD030
lem-box-perm-2341-at0312243041 : _
lem-box-perm-2341-at0312243041 = D030.lem-box-perm-2341-at0312243041 sD030
sD044 : SD044
sD044 = lem-box-tQ-at0310213442 ∷ᵃ lem-box-tQ-at0314203142 ∷ᵃ lem-box-tQ-at02142041 ∷ᵃ lem-box-tQ-at0314203241 ∷ᵃ lem-box-cP-at0213243041 ∷ᵃ lem-box-cP-at0214233041 ∷ᵃ lem-box-cP-at02132031 ∷ᵃ lem-box-perm-2314-at0213243041 ∷ᵃ lem-box-perm-1324-at02142041 ∷ᵃ lem-box-perm-2314-at0312243041 ∷ᵃ lem-box-perm-3124-at02142041 ∷ᵃ lem-box-perm-3124-at0314203241 ∷ᵃ lem-box-perm-4123-at0314203142 ∷ᵃ lem-box-box-1-at0213243041 ∷ᵃ lem-box-perm-1243-at03102132 ∷ᵃ lem-box-perm-1243-at0310213442 ∷ᵃ lem-box-perm-2341-at0312243041 ∷ᵃ nil
lem-box-box-1-at0312243041 : _
lem-box-box-1-at0312243041 = D044.lem-box-box-1-at0312243041 sD044
sD070 : SD070
sD070 = lem-box-tQ-at02142041 ∷ᵃ lem-box-tQ-at0314203241 ∷ᵃ lem-box-cP-at03143041 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-perm-2314-at0213243041 ∷ᵃ lem-box-perm-1423-at122441 ∷ᵃ lem-box2-at122441 ∷ᵃ lem-box-perm-1324-at0314203241 ∷ᵃ lem-box-perm-2314-at0312243041 ∷ᵃ lem-box-perm-3124-at02142041 ∷ᵃ lem-box-perm-3124-at0314203241 ∷ᵃ lem-CKc-box-at12213443 ∷ᵃ lem-CKc-box-at13213442 ∷ᵃ lem-box-perm-1342-at12213443 ∷ᵃ lem-box-perm-3421-at122441 ∷ᵃ lem-box-perm-4312-at13213442 ∷ᵃ lem-nf-CS-K0at2 ∷ᵃ lem-nf-CS-K1at2 ∷ᵃ lem-box-box-1-at0312243041 ∷ᵃ nil
lem-F1-CS-K0at2 : _
lem-F1-CS-K0at2 = D070.lem-F1-CS-K0at2 sD070
lem-F1-CS-K1at2 : _
lem-F1-CS-K1at2 = D070.lem-F1-CS-K1at2 sD070
sD031 : SD031
sD031 = lem-box-cP-at12233441 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-perm-1324-at122441 ∷ᵃ nil
lem-L-CCZ-1-part2 : _
lem-L-CCZ-1-part2 = D031.lem-L-CCZ-1-part2 sD031
sD045 : SD045
sD045 = lem-box-cP-at12233441 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-perm-1324-at122441 ∷ᵃ lem-box2-at243243 ∷ᵃ lem-box-perm-4132-at122441 ∷ᵃ lem-box-perm-4213-at122441 ∷ᵃ nil
lem-L-CCZ-1-part1 : _
lem-L-CCZ-1-part1 = D045.lem-L-CCZ-1-part1 sD045
lem-L-CCZ-1-part3 : _
lem-L-CCZ-1-part3 = D045.lem-L-CCZ-1-part3 sD045
sD043 : SD043
sD043 = lem-box-cP-at03243240 ∷ᵃ lem-box-cP-at033440 ∷ᵃ lem-box-perm-1324-at03243240 ∷ᵃ lem-box2-at0310243142 ∷ᵃ lem-S2-SBOX⟨0·2·43·1⟩ ∷ᵃ lem-box-perm-4213-at03243240 ∷ᵃ lem-box-perm-4132-at03243240 ∷ᵃ nil
lem-L-CX01-2 : _
lem-L-CX01-2 = D043.lem-L-CX01-2 sD043
lem-L-CX10-2 : _
lem-L-CX10-2 = D043.lem-L-CX10-2 sD043
sD022 : SD022
sD022 = lem-box-tQ-at0214203143 ∷ᵃ lem-t-cP-at0214203143 ∷ᵃ lem-box-cP-at0210243143 ∷ᵃ lem-box-cP-at0214203143 ∷ᵃ lem-box-cP-at243243 ∷ᵃ nil
lem-F4-CS2-CS2-at02132031 : _
lem-F4-CS2-CS2-at02132031 = D022.lem-F4-CS2-CS2-at02132031 sD022
lem-F4-I-CS2-at02132031 : _
lem-F4-I-CS2-at02132031 = D022.lem-F4-I-CS2-at02132031 sD022
lem-F4-S3-CS2-at02132031 : _
lem-F4-S3-CS2-at02132031 = D022.lem-F4-S3-CS2-at02132031 sD022
lem-F4-K2-CS2-at02132031 : _
lem-F4-K2-CS2-at02132031 = D022.lem-F4-K2-CS2-at02132031 sD022
lem-F4-CS2-K2-at02132031 : _
lem-F4-CS2-K2-at02132031 = D022.lem-F4-CS2-K2-at02132031 sD022
lem-F4-CS2-S3-at02132031 : _
lem-F4-CS2-S3-at02132031 = D022.lem-F4-CS2-S3-at02132031 sD022
lem-F4-CS2-I-at02132031 : _
lem-F4-CS2-I-at02132031 = D022.lem-F4-CS2-I-at02132031 sD022
lem-box2-at0214203143 : _
lem-box2-at0214203143 = D022.lem-box2-at0214203143 sD022
sD023 : SD023
sD023 = lem-sym-ab-at0214203143 ∷ᵃ lem-sym-ab-at0314203142 ∷ᵃ lem-sym-ab-at04203243 ∷ᵃ lem-sym-ab-at0213243041 ∷ᵃ lem-sym-ab-at0214233041 ∷ᵃ lem-box-tQ-at0410213243 ∷ᵃ lem-box-tQ-at0310213442 ∷ᵃ lem-box-tQ-at0214203143 ∷ᵃ lem-box-tQ-at04122041 ∷ᵃ lem-box-tQ-at04233042 ∷ᵃ lem-box-tQ-at0412213043 ∷ᵃ lem-box-tQ-at0413203142 ∷ᵃ lem-box-tQ-at0413213240 ∷ᵃ lem-box-tQ-at0440 ∷ᵃ lem-P-box-at0410233241 ∷ᵃ lem-P-box-at04103143 ∷ᵃ lem-P-box-at04122041 ∷ᵃ lem-P-box-at0412233041 ∷ᵃ lem-P-box-at0413203142 ∷ᵃ lem-P-box-at0440 ∷ᵃ lem-P-box-at0413213240 ∷ᵃ lem-box-cP-at0214203143 ∷ᵃ lem-box-cP-at0314203142 ∷ᵃ lem-box-cP-at043043 ∷ᵃ lem-pairs-at0210213443 ∷ᵃ lem-pairs-at0214233041 ∷ᵃ lem-sym-bc-at0210243143 ∷ᵃ lem-sym-bc-at0310243142 ∷ᵃ lem-CSdu-box-3-at0310213442 ∷ᵃ lem-box-cP-at0410233241 ∷ᵃ lem-box-cP-at04103143 ∷ᵃ lem-box-cP-at04122041 ∷ᵃ lem-box-cP-at0412233041 ∷ᵃ lem-box-cP-at0413203142 ∷ᵃ lem-box-cP-at0413213240 ∷ᵃ lem-box-cP-at0440 ∷ᵃ lem-box-perm-1324-at04203243 ∷ᵃ lem-pairs-at0410213243 ∷ᵃ lem-sym-bc-at04122041 ∷ᵃ lem-sym-bc-at0412233041 ∷ᵃ nil
lem-box-perm-1423-at0214203143 : _
lem-box-perm-1423-at0214203143 = D023.lem-box-perm-1423-at0214203143 sD023
sD032 : SD032
sD032 = lem-F4-I-I ∷ᵃ lem-F4-I-K0 ∷ᵃ lem-F4-I-S0 ∷ᵃ lem-F4-K0-I ∷ᵃ lem-F4-K0-K0 ∷ᵃ lem-F4-K0-S0 ∷ᵃ lem-F4-S0-I ∷ᵃ lem-F4-S0-K0 ∷ᵃ lem-F4-S0-S0 ∷ᵃ lem-sym-ab-at03102132 ∷ᵃ lem-sym-ab-at032032 ∷ᵃ lem-sym-ab-at14233142 ∷ᵃ lem-sym-ab-at03122130 ∷ᵃ lem-sym-ab-at0330 ∷ᵃ lem-sym-ab-at14213243 ∷ᵃ lem-sym-ab-at0310213442 ∷ᵃ lem-sym-ab-at0314213042 ∷ᵃ lem-sym-ab-at03203442 ∷ᵃ lem-sym-ab-at03243042 ∷ᵃ lem-sym-ab-at142142 ∷ᵃ lem-sym-ab-at2442 ∷ᵃ lem-sym-bc-at03102132 ∷ᵃ lem-sym-bc-at0310213442 ∷ᵃ lem-box-cP-at0214233041 ∷ᵃ lem-box-cP-at0210243143 ∷ᵃ lem-box-cP-at0214203143 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-sym-bc-at0310243142 ∷ᵃ lem-sym-bc-at031031 ∷ᵃ lem-sym-bc-at132132 ∷ᵃ lem-sym-bc-at1331 ∷ᵃ lem-sym-bc-at243243 ∷ᵃ lem-F4-I-CS0 ∷ᵃ lem-F4-K0-CS0 ∷ᵃ lem-F4-S0-CS0 ∷ᵃ lem-Xb-box-at0210243143 ∷ᵃ lem-Xb-box-at243243 ∷ᵃ lem-box2-at0210243143 ∷ᵃ lem-box2-at243243 ∷ᵃ lem-pairs-at0310243142 ∷ᵃ lem-pairs-at0330 ∷ᵃ lem-pairs-at1331 ∷ᵃ lem-pairs-at3443 ∷ᵃ lem-pairs-at031031 ∷ᵃ lem-pairs-at03243042 ∷ᵃ lem-pairs-at2442 ∷ᵃ lem-box2-at0214203143 ∷ᵃ lem-box-perm-1423-at0214203143 ∷ᵃ nil
lem-box-perm-2341-at03122130 : _
lem-box-perm-2341-at03122130 = D032.lem-box-perm-2341-at03122130 sD032
lem-box-perm-4123-at03203442 : _
lem-box-perm-4123-at03203442 = D032.lem-box-perm-4123-at03203442 sD032
lem-box-perm-4123-at14213243 : _
lem-box-perm-4123-at14213243 = D032.lem-box-perm-4123-at14213243 sD032
lem-F5-23-at02132031 : _
lem-F5-23-at02132031 = D032.lem-F5-23-at02132031 sD032
sD046 : SD046
sD046 = lem-F4-I-K2 ∷ᵃ lem-F4-I-S3 ∷ᵃ lem-F4-K2-K2 ∷ᵃ lem-F4-S3-I ∷ᵃ lem-F4-S3-K2 ∷ᵃ lem-F4-S3-S3 ∷ᵃ lem-F4-I-K2-at02132031 ∷ᵃ lem-F4-I-S3-at02132031 ∷ᵃ lem-F4-K2-K2-at02132031 ∷ᵃ lem-F4-S3-I-at02132031 ∷ᵃ lem-F4-S3-K2-at02132031 ∷ᵃ lem-F4-S3-S3-at02132031 ∷ᵃ lem-box-tQ-at03203442 ∷ᵃ lem-box-tQ-at14213243 ∷ᵃ lem-box-cP-at02132130 ∷ᵃ lem-box-cP-at0310243142 ∷ᵃ lem-F4-CS2-I ∷ᵃ lem-F4-CS2-S3 ∷ᵃ lem-F4-I-CS2 ∷ᵃ lem-F4-K2-CS2 ∷ᵃ lem-F4-S3-CS2 ∷ᵃ lem-F4-CS2-K2 ∷ᵃ lem-F4-CS2-CS2 ∷ᵃ lem-box-perm-2341-at13243142 ∷ᵃ lem-F4-CS2-CS2-at02132031 ∷ᵃ lem-F4-CS2-I-at02132031 ∷ᵃ lem-F4-CS2-K2-at02132031 ∷ᵃ lem-F4-CS2-S3-at02132031 ∷ᵃ lem-F4-I-CS2-at02132031 ∷ᵃ lem-F4-K2-CS2-at02132031 ∷ᵃ lem-F4-S3-CS2-at02132031 ∷ᵃ lem-F5-23 ∷ᵃ lem-F5-23-at02132031 ∷ᵃ lem-box-perm-2341-at03122130 ∷ᵃ lem-box-perm-4123-at03203442 ∷ᵃ lem-box-perm-4123-at14213243 ∷ᵃ nil
lem-box-box-1-at03122130 : _
lem-box-box-1-at03122130 = D046.lem-box-box-1-at03122130 sD046
lem-box-box-1-at13243142 : _
lem-box-box-1-at13243142 = D046.lem-box-box-1-at13243142 sD046
sD071 : SD071
sD071 = lem-box-tQ-at0220 ∷ᵃ lem-box-tQ-at032032 ∷ᵃ lem-box-tQ-at0314213042 ∷ᵃ lem-box-tQ-at142142 ∷ᵃ lem-box-cP-at14233142 ∷ᵃ lem-box-cP-at0330 ∷ᵃ lem-box-cP-at12233441 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-box-perm-1324-at032032 ∷ᵃ lem-box-perm-2314-at13243142 ∷ᵃ lem-box-perm-3124-at0220 ∷ᵃ lem-box-perm-3124-at032032 ∷ᵃ lem-box-perm-1324-at122441 ∷ᵃ lem-box-perm-2314-at0310243142 ∷ᵃ lem-box-perm-3124-at0314213042 ∷ᵃ lem-box-perm-1324-at142142 ∷ᵃ lem-box-perm-2314-at02132130 ∷ᵃ lem-box-perm-2314-at03122130 ∷ᵃ lem-box-perm-3124-at142142 ∷ᵃ lem-S2-SBOX⟨0·2·43·1⟩ ∷ᵃ lem-L-CX01-1 ∷ᵃ lem-L-CX01-2 ∷ᵃ lem-L-CX10-2 ∷ᵃ lem-box-box-1-at03122130 ∷ᵃ lem-box-box-1-at13243142 ∷ᵃ nil
lem-L-CCZ-1-part0 : _
lem-L-CCZ-1-part0 = D071.lem-L-CCZ-1-part0 sD071
sD147 : SD147
sD147 = lem-F1-order-Iat0 ∷ᵃ lem-F1-order-Kat2 ∷ᵃ lem-F1-order-Kat3 ∷ᵃ lem-F1-order-SKat2 ∷ᵃ lem-F1-order-SKat3 ∷ᵃ lem-F1-order-Sat2 ∷ᵃ lem-F1-order-Sat3 ∷ᵃ lem-F2-I-K0 ∷ᵃ lem-F2-I-K1 ∷ᵃ lem-F2-I-K2 ∷ᵃ lem-F2-I-K3 ∷ᵃ lem-F2-I-S0 ∷ᵃ lem-F2-I-S1 ∷ᵃ lem-F2-I-S2 ∷ᵃ lem-F2-I-S3 ∷ᵃ lem-F2-K0-K1 ∷ᵃ lem-F2-K0-K2 ∷ᵃ lem-F2-K0-K3 ∷ᵃ lem-F2-K1-K2 ∷ᵃ lem-F2-K1-K3 ∷ᵃ lem-F2-K2-K3 ∷ᵃ lem-F2-S0-K1 ∷ᵃ lem-F2-S0-K2 ∷ᵃ lem-F2-S0-K3 ∷ᵃ lem-F2-S0-S1 ∷ᵃ lem-F2-S0-S2 ∷ᵃ lem-F2-S0-S3 ∷ᵃ lem-F2-S1-K0 ∷ᵃ lem-F2-S1-K2 ∷ᵃ lem-F2-S1-K3 ∷ᵃ lem-F2-S1-S2 ∷ᵃ lem-F2-S1-S3 ∷ᵃ lem-F2-S2-K0 ∷ᵃ lem-F2-S2-K1 ∷ᵃ lem-F2-S2-K3 ∷ᵃ lem-F2-S2-S3 ∷ᵃ lem-F2-S3-K0 ∷ᵃ lem-F2-S3-K1 ∷ᵃ lem-F2-S3-K2 ∷ᵃ lem-F2-S0-CS1 ∷ᵃ lem-F2-S0-CS2 ∷ᵃ lem-F2-S2-CS0 ∷ᵃ lem-CXAu-S ∷ᵃ lem-F2-I-CS0 ∷ᵃ lem-F2-I-CS1 ∷ᵃ lem-F2-I-CS2 ∷ᵃ lem-F2-S1-CS2 ∷ᵃ lem-F2-S3-CS0 ∷ᵃ lem-F2-S3-CS1 ∷ᵃ lem-CXAu-S-at14213243 ∷ᵃ lem-F2-K1-CS2 ∷ᵃ lem-F1-comm-CS-S0at2 ∷ᵃ lem-F2-K3-CS0 ∷ᵃ lem-F2-K3-CS1 ∷ᵃ lem-CXAu-S-at01143043 ∷ᵃ lem-F1-comm-CS-S1at2 ∷ᵃ lem-L-CCZ-1-part2 ∷ᵃ lem-F1-order-CSat2 ∷ᵃ lem-F2-K0-CS1 ∷ᵃ lem-F2-K0-CS2 ∷ᵃ lem-F2-K2-CS0 ∷ᵃ lem-L-CCZ-1-part1 ∷ᵃ lem-L-CCZ-1-part3 ∷ᵃ lem-CXuA-S ∷ᵃ lem-CXuA-S-at14213243 ∷ᵃ lem-F1-X-CS0at2 ∷ᵃ lem-F2-CS0-CS2 ∷ᵃ lem-CXuA-S-at01143043 ∷ᵃ lem-F1-X-CS1at2 ∷ᵃ lem-F1-CS-K0at2 ∷ᵃ lem-F1-CS-K1at2 ∷ᵃ lem-L-CCZ-1-part0 ∷ᵃ nil
lem-SW-S : _
lem-SW-S = D147.lem-SW-S sD147
lem-SW-S-at14213243 : _
lem-SW-S-at14213243 = D147.lem-SW-S-at14213243 sD147
lem-SW-S-at01143043 : _
lem-SW-S-at01143043 = D147.lem-SW-S-at01143043 sD147
lem-deb-P-hi-eps : _
lem-deb-P-hi-eps = D147.lem-deb-P-hi-eps sD147
sD189 : SD189
sD189 = lem-F4-I-I ∷ᵃ lem-F4-I-K2 ∷ᵃ lem-F4-I-S2 ∷ᵃ lem-F4-I-S3 ∷ᵃ lem-F4-K2-I ∷ᵃ lem-F4-K2-K2 ∷ᵃ lem-F4-K2-S2 ∷ᵃ lem-F4-K2-S3 ∷ᵃ lem-F4-S3-I ∷ᵃ lem-F4-S3-K2 ∷ᵃ lem-F4-S3-S2 ∷ᵃ lem-F4-S3-S3 ∷ᵃ lem-nat-S ∷ᵃ lem-nat-S-at14213243 ∷ᵃ lem-F1-order-Iat0 ∷ᵃ lem-F1-order-Kat2 ∷ᵃ lem-F1-order-Kat3 ∷ᵃ lem-F1-order-SKat2 ∷ᵃ lem-F1-order-SKat3 ∷ᵃ lem-F1-order-Sat2 ∷ᵃ lem-F1-order-Sat3 ∷ᵃ lem-F2-I-K0 ∷ᵃ lem-F2-I-K1 ∷ᵃ lem-F2-I-K2 ∷ᵃ lem-F2-I-K3 ∷ᵃ lem-F2-I-S0 ∷ᵃ lem-F2-I-S1 ∷ᵃ lem-F2-I-S2 ∷ᵃ lem-F2-I-S3 ∷ᵃ lem-F2-K0-K1 ∷ᵃ lem-F2-K0-K2 ∷ᵃ lem-F2-K0-K3 ∷ᵃ lem-F2-K1-K2 ∷ᵃ lem-F2-K1-K3 ∷ᵃ lem-F2-K2-K3 ∷ᵃ lem-F2-S0-K1 ∷ᵃ lem-F2-S0-K2 ∷ᵃ lem-F2-S0-K3 ∷ᵃ lem-F2-S0-S1 ∷ᵃ lem-F2-S0-S2 ∷ᵃ lem-F2-S0-S3 ∷ᵃ lem-F2-S1-K0 ∷ᵃ lem-F2-S1-K2 ∷ᵃ lem-F2-S1-K3 ∷ᵃ lem-F2-S1-S2 ∷ᵃ lem-F2-S1-S3 ∷ᵃ lem-F2-S2-K0 ∷ᵃ lem-F2-S2-K1 ∷ᵃ lem-F2-S2-K3 ∷ᵃ lem-F2-S2-S3 ∷ᵃ lem-F2-S3-K0 ∷ᵃ lem-F2-S3-K1 ∷ᵃ lem-F2-S3-K2 ∷ᵃ lem-nat-S-at01143043 ∷ᵃ lem-F2-S0-CS1 ∷ᵃ lem-F2-S0-CS2 ∷ᵃ lem-F2-S2-CS0 ∷ᵃ lem-F4-CS2-I ∷ᵃ lem-F4-CS2-S2 ∷ᵃ lem-F4-CS2-S3 ∷ᵃ lem-F4-I-CS2 ∷ᵃ lem-F4-K2-CS2 ∷ᵃ lem-F4-S3-CS2 ∷ᵃ lem-F4-CS2-K2 ∷ᵃ lem-F2-I-CS0 ∷ᵃ lem-F2-I-CS1 ∷ᵃ lem-F2-I-CS2 ∷ᵃ lem-F2-S1-CS2 ∷ᵃ lem-F2-S3-CS0 ∷ᵃ lem-F2-S3-CS1 ∷ᵃ lem-F4-CS2-CS2 ∷ᵃ lem-F2-K1-CS2 ∷ᵃ lem-F1-comm-CS-S0at2 ∷ᵃ lem-F2-K3-CS0 ∷ᵃ lem-F2-K3-CS1 ∷ᵃ lem-S2-SBOX⟨0·2·43·1⟩ ∷ᵃ lem-F1-comm-CS-S1at2 ∷ᵃ lem-F1-order-CSat2 ∷ᵃ lem-F2-K0-CS1 ∷ᵃ lem-F2-K0-CS2 ∷ᵃ lem-F2-K2-CS0 ∷ᵃ lem-F1-X-CS0at2 ∷ᵃ lem-F2-CS0-CS2 ∷ᵃ lem-F1-X-CS1at2 ∷ᵃ lem-F1-CS-K0at2 ∷ᵃ lem-F1-CS-K1at2 ∷ᵃ lem-SW-S ∷ᵃ lem-SW-S-at01143043 ∷ᵃ lem-SW-S-at14213243 ∷ᵃ lem-deb-P-hi-eps ∷ᵃ nil
lem-F0-at14213243 : _
lem-F0-at14213243 = D189.lem-F0-at14213243 sD189
lem-F0-at01143043 : _
lem-F0-at01143043 = D189.lem-F0-at01143043 sD189
sD204 : SD204
sD204 = lem-box-cP-at0310243142 ∷ᵃ lem-box-cP-at03243240 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-box-cP-at3443 ∷ᵃ lem-box-perm-1324-at243243 ∷ᵃ lem-CSdu-box-3-at0310243142 ∷ᵃ lem-CSdu-box-3-at243243 ∷ᵃ lem-CSu-box-3-at0310243142 ∷ᵃ lem-CSu-box-3-at243243 ∷ᵃ lem-CXu-box-4-at0310243142 ∷ᵃ lem-box2-at03243240 ∷ᵃ lem-box-perm-1342-at0310243142 ∷ᵃ lem-box-perm-1342-at243243 ∷ᵃ lem-box-perm-1423 ∷ᵃ lem-box-perm-1423-at03102132 ∷ᵃ lem-box-perm-2431-at132132 ∷ᵃ lem-box-perm-4132-at243243 ∷ᵃ lem-box-perm-3241-at0310243142 ∷ᵃ lem-box-box-1-at03102132 ∷ᵃ lem-box-box-3 ∷ᵃ lem-F0-at01143043 ∷ᵃ lem-F0-at14213243 ∷ᵃ nil
lem-F4-CS0-CS1 : _
lem-F4-CS0-CS1 = D204.lem-F4-CS0-CS1 sD204
lem-F4-CS1-CS0 : _
lem-F4-CS1-CS0 = D204.lem-F4-CS1-CS0 sD204
