------------------------------------------------------------------------
-- Presentations of groups
--
-- Lists of four-wire macro letters as strings
--
-- `ℓ s` is the list of the macro letters the characters of s stand
-- for, the n-th letter of Mac being U+4E00 + n.  The derivation modules
-- of Four/D and the statement trees spell their letter lists this way:
-- a string is one token, where a list of letters was a chain of `_∷_`
-- for the operator parser and a term per letter for the elaborator.
-- Written by `scratchpad/four/strings.py`, which rewrites the lists.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Str where

open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Agda.Builtin.String using (String ; primStringToList)

open import Examples.Groups.Clifford+CS.Four.Letters

chM : Char → Mac
chM '一' = ι
chM '丁' = ι1
chM '丂' = ι2
chM '七' = ι3
chM '丄' = ι⁻
chM '丅' = ι1⁻
chM '丆' = ι2⁻
chM '万' = ι3⁻
chM '丈' = S0
chM '三' = S0⁻
chM '上' = K0
chM '下' = K0⁻
chM '丌' = X0
chM '不' = Z0
chM '与' = S1
chM '丏' = S1⁻
chM '丐' = K1
chM '丑' = K1⁻
chM '丒' = X1
chM '专' = Z1
chM '且' = S2
chM '丕' = S2⁻
chM '世' = K2
chM '丗' = K2⁻
chM '丘' = X2
chM '丙' = Z2
chM '业' = S3
chM '丛' = S3⁻
chM '东' = K3
chM '丝' = K3⁻
chM '丞' = X3
chM '丟' = Z3
chM '丠' = CS01
chM '両' = CS01⁻
chM '丢' = CZ01
chM '丣' = CX01
chM '两' = CK01
chM '严' = CK01⁻
chM '並' = Sw01
chM '丧' = CS02
chM '丨' = CS02⁻
chM '丩' = CZ02
chM '个' = CX02
chM '丫' = CK02
chM '丬' = CK02⁻
chM '中' = CS03
chM '丮' = CS03⁻
chM '丯' = CZ03
chM '丰' = CX03
chM '丱' = CK03
chM '串' = CK03⁻
chM '丳' = CX10
chM '临' = CK10
chM '丵' = CK10⁻
chM '丶' = CS12
chM '丷' = CS12⁻
chM '丸' = CZ12
chM '丹' = CX12
chM '为' = CK12
chM '主' = CK12⁻
chM '丼' = Sw12
chM '丽' = CS13
chM '举' = CS13⁻
chM '丿' = CZ13
chM '乀' = CX13
chM '乁' = CK13
chM '乂' = CK13⁻
chM '乃' = CX20
chM '乄' = CK20
chM '久' = CK20⁻
chM '乆' = CX21
chM '乇' = CK21
chM '么' = CK21⁻
chM '义' = CS23
chM '乊' = CS23⁻
chM '之' = CZ23
chM '乌' = CX23
chM '乍' = CK23
chM '乎' = CK23⁻
chM '乏' = Sw23
chM '乐' = CX30
chM '乑' = CK30
chM '乒' = CK30⁻
chM '乓' = CX31
chM '乔' = CK31
chM '乕' = CK31⁻
chM '乖' = CX32
chM '乗' = CK32
chM '乘' = CK32⁻
chM '乙' = CCZ012
chM '乚' = CCZ013
chM '乛' = CCZ023
chM '乜' = CCZ123
chM '九' = Toff012
chM '乞' = Toff013
chM '也' = Toff023
chM '习' = Toff102
chM '乡' = Toff103
chM '乢' = Toff123
chM '乣' = Toff201
chM '乤' = Toff203
chM '乥' = Toff213
chM '书' = Toff301
chM '乧' = Toff302
chM '乨' = Toff312
chM _   = ι

private
  dec : List Char → List Mac
  dec []       = []
  dec (c ∷ cs) = chM c ∷ dec cs

ℓ : String → List Mac
ℓ s = dec (primStringToList s)
