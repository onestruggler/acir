------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the four-wire derivations, each decided once
--
-- Each lemma is one window step of Four/D: two words on three wires with
-- the same operator, equal by completeness on three wires
-- (Windows.win, one evaluation, through the tables of Four.Lits),
-- stated over the macro letters as Four/D uses it.  Written by
-- scratchpad/four/winlib4.py, restated by winmac4.py and wintable4.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Wins.W01 where

open import Data.List.Base using ([] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Four.Lits using (lw0 ; lw1 ; lw2 ; lw3)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)

wn00001 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "乏乏") ⟫ʷ
wn00001 b = lw0 b [] (ℓ "乏乏") tt tt Eq.refl
wn00002 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "乃乃") ⟫ʷ
wn00002 b = lw3 b [] (ℓ "乃乃") tt tt Eq.refl
wn00003 : Base 3 → ⟪ (ℓ "乏乏") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00003 b = lw0 b (ℓ "乏乏") [] tt tt Eq.refl
wn00004 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "乙乙") ⟫ʷ
wn00004 b = lw3 b [] (ℓ "乙乙") tt tt Eq.refl
wn00005 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "並並") ⟫ʷ
wn00005 b = lw3 b [] (ℓ "並並") tt tt Eq.refl
wn00006 : Base 3 → ⟪ (ℓ "乃並") ⟫ʷ ≈ ⟪ (ℓ "並乆") ⟫ʷ
wn00006 b = lw3 b (ℓ "乃並") (ℓ "並乆") tt tt Eq.refl
wn00007 : Base 3 → ⟪ (ℓ "丧並") ⟫ʷ ≈ ⟪ (ℓ "並丶") ⟫ʷ
wn00007 b = lw3 b (ℓ "丧並") (ℓ "並丶") tt tt Eq.refl
wn00008 : Base 3 → ⟪ (ℓ "丣並") ⟫ʷ ≈ ⟪ (ℓ "並丳") ⟫ʷ
wn00008 b = lw3 b (ℓ "丣並") (ℓ "並丳") tt tt Eq.refl
wn00009 : Base 3 → ⟪ (ℓ "丷並") ⟫ʷ ≈ ⟪ (ℓ "並丨") ⟫ʷ
wn00009 b = lw3 b (ℓ "丷並") (ℓ "並丨") tt tt Eq.refl
wn00010 : Base 3 → ⟪ (ℓ "丶並") ⟫ʷ ≈ ⟪ (ℓ "並丧") ⟫ʷ
wn00010 b = lw3 b (ℓ "丶並") (ℓ "並丧") tt tt Eq.refl
wn00011 : Base 3 → ⟪ (ℓ "丧丳丨丳丶") ⟫ʷ ≈ ⟪ (ℓ "丶丣丷丣丧") ⟫ʷ
wn00011 b = lw3 b (ℓ "丧丳丨丳丶") (ℓ "丶丣丷丣丧") tt tt Eq.refl
wn00012 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "丼丼") ⟫ʷ
wn00012 b = lw3 b [] (ℓ "丼丼") tt tt Eq.refl
wn00013 : Base 3 → ⟪ (ℓ "乓丼") ⟫ʷ ≈ ⟪ (ℓ "丼乖") ⟫ʷ
wn00013 b = lw0 b (ℓ "乓丼") (ℓ "丼乖") tt tt Eq.refl
wn00014 : Base 3 → ⟪ (ℓ "丼丼") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00014 b = lw3 b (ℓ "丼丼") [] tt tt Eq.refl
wn00015 : Base 3 → ⟪ (ℓ "丷丼") ⟫ʷ ≈ ⟪ (ℓ "丼丷") ⟫ʷ
wn00015 b = lw3 b (ℓ "丷丼") (ℓ "丼丷") tt tt Eq.refl
wn00016 : Base 3 → ⟪ (ℓ "丶丼") ⟫ʷ ≈ ⟪ (ℓ "丼丶") ⟫ʷ
wn00016 b = lw3 b (ℓ "丶丼") (ℓ "丼丶") tt tt Eq.refl
wn00017 : Base 3 → ⟪ (ℓ "丶个丷个丠") ⟫ʷ ≈ ⟪ (ℓ "丶丣丷丣丧") ⟫ʷ
wn00017 b = lw3 b (ℓ "丶个丷个丠") (ℓ "丶丣丷丣丧") tt tt Eq.refl
wn00018 : Base 3 → ⟪ (ℓ "丼丶") ⟫ʷ ≈ ⟪ (ℓ "丶丼") ⟫ʷ
wn00018 b = lw3 b (ℓ "丼丶") (ℓ "丶丼") tt tt Eq.refl
wn00019 : Base 3 → ⟪ (ℓ "丼丷") ⟫ʷ ≈ ⟪ (ℓ "丷丼") ⟫ʷ
wn00019 b = lw3 b (ℓ "丼丷") (ℓ "丷丼") tt tt Eq.refl
wn00020 : Base 3 → ⟪ (ℓ "丼丽") ⟫ʷ ≈ ⟪ (ℓ "义丼") ⟫ʷ
wn00020 b = lw0 b (ℓ "丼丽") (ℓ "义丼") tt tt Eq.refl
wn00021 : Base 3 → ⟪ (ℓ "丼举") ⟫ʷ ≈ ⟪ (ℓ "乊丼") ⟫ʷ
wn00021 b = lw0 b (ℓ "丼举") (ℓ "乊丼") tt tt Eq.refl
wn00022 : Base 3 → ⟪ (ℓ "丼乏丼") ⟫ʷ ≈ ⟪ (ℓ "乏丼乏") ⟫ʷ
wn00022 b = lw0 b (ℓ "丼乏丼") (ℓ "乏丼乏") tt tt Eq.refl
wn00023 : Base 3 → ⟪ (ℓ "乏丼乏") ⟫ʷ ≈ ⟪ (ℓ "丼乏丼") ⟫ʷ
wn00023 b = lw0 b (ℓ "乏丼乏") (ℓ "丼乏丼") tt tt Eq.refl
wn00024 : Base 3 → ⟪ (ℓ "並个") ⟫ʷ ≈ ⟪ (ℓ "丹並") ⟫ʷ
wn00024 b = lw3 b (ℓ "並个") (ℓ "丹並") tt tt Eq.refl
wn00025 : Base 3 → ⟪ (ℓ "並丧") ⟫ʷ ≈ ⟪ (ℓ "丶並") ⟫ʷ
wn00025 b = lw3 b (ℓ "並丧") (ℓ "丶並") tt tt Eq.refl
wn00026 : Base 3 → ⟪ (ℓ "义丹乊丹丽") ⟫ʷ ≈ ⟪ (ℓ "义丹乊丹丽") ⟫ʷ
wn00026 b = lw0 b (ℓ "义丹乊丹丽") (ℓ "义丹乊丹丽") tt tt Eq.refl
wn00027 : Base 3 → ⟪ (ℓ "並丶") ⟫ʷ ≈ ⟪ (ℓ "丧並") ⟫ʷ
wn00027 b = lw3 b (ℓ "並丶") (ℓ "丧並") tt tt Eq.refl
wn00028 : Base 3 → ⟪ (ℓ "並丣") ⟫ʷ ≈ ⟪ (ℓ "丳並") ⟫ʷ
wn00028 b = lw3 b (ℓ "並丣") (ℓ "丳並") tt tt Eq.refl
wn00029 : Base 3 → ⟪ (ℓ "並丷") ⟫ʷ ≈ ⟪ (ℓ "丨並") ⟫ʷ
wn00029 b = lw3 b (ℓ "並丷") (ℓ "丨並") tt tt Eq.refl
wn00030 : Base 3 → ⟪ (ℓ "並丹") ⟫ʷ ≈ ⟪ (ℓ "个並") ⟫ʷ
wn00030 b = lw3 b (ℓ "並丹") (ℓ "个並") tt tt Eq.refl
wn00031 : Base 3 → ⟪ (ℓ "並並") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00031 b = lw3 b (ℓ "並並") [] tt tt Eq.refl
wn00032 : Base 3 → ⟪ (ℓ "乙乙") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00032 b = lw3 b (ℓ "乙乙") [] tt tt Eq.refl
wn00033 : Base 3 → ⟪ (ℓ "乜乜") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00033 b = lw0 b (ℓ "乜乜") [] tt tt Eq.refl
wn00034 : Base 3 → ⟪ (ℓ "乜") ⟫ʷ ≈ ⟪ (ℓ "义丹乊丹丽") ⟫ʷ
wn00034 b = lw0 b (ℓ "乜") (ℓ "义丹乊丹丽") tt tt Eq.refl
wn00035 : Base 3 → ⟪ (ℓ "丶乃") ⟫ʷ ≈ ⟪ (ℓ "乃丶") ⟫ʷ
wn00035 b = lw3 b (ℓ "丶乃") (ℓ "乃丶") tt tt Eq.refl
wn00036 : Base 3 → ⟪ (ℓ "乀丼") ⟫ʷ ≈ ⟪ (ℓ "丼乌") ⟫ʷ
wn00036 b = lw0 b (ℓ "乀丼") (ℓ "丼乌") tt tt Eq.refl
wn00037 : Base 3 → ⟪ (ℓ "乌丼") ⟫ʷ ≈ ⟪ (ℓ "丼乀") ⟫ʷ
wn00037 b = lw0 b (ℓ "乌丼") (ℓ "丼乀") tt tt Eq.refl
wn00038 : Base 3 → ⟪ (ℓ "乊乓") ⟫ʷ ≈ ⟪ (ℓ "乓乊") ⟫ʷ
wn00038 b = lw0 b (ℓ "乊乓") (ℓ "乓乊") tt tt Eq.refl
wn00039 : Base 3 → ⟪ (ℓ "並乆") ⟫ʷ ≈ ⟪ (ℓ "乃並") ⟫ʷ
wn00039 b = lw3 b (ℓ "並乆") (ℓ "乃並") tt tt Eq.refl
wn00040 : Base 3 → ⟪ (ℓ "义乓") ⟫ʷ ≈ ⟪ (ℓ "乓义") ⟫ʷ
wn00040 b = lw0 b (ℓ "义乓") (ℓ "乓义") tt tt Eq.refl
wn00041 : Base 3 → ⟪ (ℓ "义丹乊丹丽") ⟫ʷ ≈ ⟪ (ℓ "乜") ⟫ʷ
wn00041 b = lw0 b (ℓ "义丹乊丹丽") (ℓ "乜") tt tt Eq.refl
wn00042 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "乌乌") ⟫ʷ
wn00042 b = lw0 b [] (ℓ "乌乌") tt tt Eq.refl
wn00043 : Base 3 → ⟪ (ℓ "丶丣丷丣丧") ⟫ʷ ≈ ⟪ (ℓ "丶丣丷丣丧") ⟫ʷ
wn00043 b = lw3 b (ℓ "丶丣丷丣丧") (ℓ "丶丣丷丣丧") tt tt Eq.refl
wn00044 : Base 3 → ⟪ (ℓ "乌乏") ⟫ʷ ≈ ⟪ (ℓ "乏乖") ⟫ʷ
wn00044 b = lw0 b (ℓ "乌乏") (ℓ "乏乖") tt tt Eq.refl
wn00045 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "九九") ⟫ʷ
wn00045 b = lw3 b [] (ℓ "九九") tt tt Eq.refl
wn00046 : Base 3 → ⟪ (ℓ "上丶个丷个丠上一") ⟫ʷ ≈ ⟪ (ℓ "上丶丣丷丣丧上一") ⟫ʷ
wn00046 b = lw3 b (ℓ "上丶个丷个丠上一") (ℓ "上丶丣丷丣丧上一") tt tt Eq.refl
wn00047 : Base 3 → ⟪ (ℓ "乊丼") ⟫ʷ ≈ ⟪ (ℓ "丼举") ⟫ʷ
wn00047 b = lw0 b (ℓ "乊丼") (ℓ "丼举") tt tt Eq.refl
wn00048 : Base 3 → ⟪ (ℓ "义丼") ⟫ʷ ≈ ⟪ (ℓ "丼丽") ⟫ʷ
wn00048 b = lw0 b (ℓ "义丼") (ℓ "丼丽") tt tt Eq.refl
wn00049 : Base 3 → ⟪ (ℓ "丼义") ⟫ʷ ≈ ⟪ (ℓ "丽丼") ⟫ʷ
wn00049 b = lw0 b (ℓ "丼义") (ℓ "丽丼") tt tt Eq.refl
wn00050 : Base 3 → ⟪ (ℓ "丼丹") ⟫ʷ ≈ ⟪ (ℓ "乆丼") ⟫ʷ
wn00050 b = lw3 b (ℓ "丼丹") (ℓ "乆丼") tt tt Eq.refl
wn00051 : Base 3 → ⟪ (ℓ "丼乊") ⟫ʷ ≈ ⟪ (ℓ "举丼") ⟫ʷ
wn00051 b = lw0 b (ℓ "丼乊") (ℓ "举丼") tt tt Eq.refl
wn00052 : Base 3 → ⟪ (ℓ "丽乆举乆义") ⟫ʷ ≈ ⟪ (ℓ "义丹乊丹丽") ⟫ʷ
wn00052 b = lw0 b (ℓ "丽乆举乆义") (ℓ "义丹乊丹丽") tt tt Eq.refl
wn00053 : Base 3 → ⟪ (ℓ "九") ⟫ʷ ≈ ⟪ (ℓ "上乙下") ⟫ʷ
wn00053 b = lw3 b (ℓ "九") (ℓ "上乙下") tt tt Eq.refl
wn00054 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "下上") ⟫ʷ
wn00054 b = lw3 b [] (ℓ "下上") tt tt Eq.refl
wn00055 : Base 3 → ⟪ (ℓ "上乙下") ⟫ʷ ≈ ⟪ (ℓ "九") ⟫ʷ
wn00055 b = lw3 b (ℓ "上乙下") (ℓ "九") tt tt Eq.refl
wn00056 : Base 3 → ⟪ (ℓ "上丶丣丷丣丧上一") ⟫ʷ ≈ ⟪ (ℓ "上丶丣丷丣丧上一") ⟫ʷ
wn00056 b = lw3 b (ℓ "上丶丣丷丣丧上一") (ℓ "上丶丣丷丣丧上一") tt tt Eq.refl
wn00057 : Base 3 → ⟪ (ℓ "九") ⟫ʷ ≈ ⟪ (ℓ "上丠乆両乆丧下") ⟫ʷ
wn00057 b = lw3 b (ℓ "九") (ℓ "上丠乆両乆丧下") tt tt Eq.refl
wn00058 : Base 3 → ⟪ (ℓ "乌乆") ⟫ʷ ≈ ⟪ (ℓ "乆乌") ⟫ʷ
wn00058 b = lw0 b (ℓ "乌乆") (ℓ "乆乌") tt tt Eq.refl
wn00059 : Base 3 → ⟪ (ℓ "乌丶") ⟫ʷ ≈ ⟪ (ℓ "丶乌") ⟫ʷ
wn00059 b = lw0 b (ℓ "乌丶") (ℓ "丶乌") tt tt Eq.refl
wn00060 : Base 3 → ⟪ (ℓ "乌乌") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00060 b = lw0 b (ℓ "乌乌") [] tt tt Eq.refl
wn00061 : Base 3 → ⟪ (ℓ "上丠乆両乆丧下") ⟫ʷ ≈ ⟪ (ℓ "九") ⟫ʷ
wn00061 b = lw3 b (ℓ "上丠乆両乆丧下") (ℓ "九") tt tt Eq.refl
wn00062 : Base 3 → ⟪ (ℓ "乏乆") ⟫ʷ ≈ ⟪ (ℓ "乓乏") ⟫ʷ
wn00062 b = lw0 b (ℓ "乏乆") (ℓ "乓乏") tt tt Eq.refl
wn00063 : Base 3 → ⟪ (ℓ "乏丶") ⟫ʷ ≈ ⟪ (ℓ "丽乏") ⟫ʷ
wn00063 b = lw0 b (ℓ "乏丶") (ℓ "丽乏") tt tt Eq.refl
wn00064 : Base 3 → ⟪ (ℓ "九") ⟫ʷ ≈ ⟪ (ℓ "上丧丹丨丹丠下") ⟫ʷ
wn00064 b = lw3 b (ℓ "九") (ℓ "上丧丹丨丹丠下") tt tt Eq.refl
wn00065 : Base 3 → ⟪ (ℓ "丽丼") ⟫ʷ ≈ ⟪ (ℓ "丼义") ⟫ʷ
wn00065 b = lw0 b (ℓ "丽丼") (ℓ "丼义") tt tt Eq.refl
wn00066 : Base 3 → ⟪ (ℓ "丽丹") ⟫ʷ ≈ ⟪ (ℓ "丹丽") ⟫ʷ
wn00066 b = lw0 b (ℓ "丽丹") (ℓ "丹丽") tt tt Eq.refl
wn00067 : Base 3 → ⟪ (ℓ "丶丠") ⟫ʷ ≈ ⟪ (ℓ "丠丶") ⟫ʷ
wn00067 b = lw3 b (ℓ "丶丠") (ℓ "丠丶") tt tt Eq.refl
wn00068 : Base 3 → ⟪ (ℓ "上丧丹丨丹丠下") ⟫ʷ ≈ ⟪ (ℓ "九") ⟫ʷ
wn00068 b = lw3 b (ℓ "上丧丹丨丹丠下") (ℓ "九") tt tt Eq.refl
wn00069 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "丳丳") ⟫ʷ
wn00069 b = lw3 b [] (ℓ "丳丳") tt tt Eq.refl
wn00070 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "乜乜") ⟫ʷ
wn00070 b = lw0 b [] (ℓ "乜乜") tt tt Eq.refl
wn00071 : Base 3 → ⟪ (ℓ "乏义") ⟫ʷ ≈ ⟪ (ℓ "义乏") ⟫ʷ
wn00071 b = lw0 b (ℓ "乏义") (ℓ "义乏") tt tt Eq.refl
wn00072 : Base 3 → ⟪ (ℓ "乏乊") ⟫ʷ ≈ ⟪ (ℓ "乊乏") ⟫ʷ
wn00072 b = lw0 b (ℓ "乏乊") (ℓ "乊乏") tt tt Eq.refl
wn00073 : Base 3 → ⟪ (ℓ "义乀乊乀丶") ⟫ʷ ≈ ⟪ (ℓ "义丹乊丹丽") ⟫ʷ
wn00073 b = lw0 b (ℓ "义乀乊乀丶") (ℓ "义丹乊丹丽") tt tt Eq.refl
wn00074 : Base 3 → ⟪ (ℓ "个並") ⟫ʷ ≈ ⟪ (ℓ "並丹") ⟫ʷ
wn00074 b = lw3 b (ℓ "个並") (ℓ "並丹") tt tt Eq.refl
wn00075 : Base 3 → ⟪ (ℓ "乜") ⟫ʷ ≈ ⟪ (ℓ "丶乓丷乓义") ⟫ʷ
wn00075 b = lw0 b (ℓ "乜") (ℓ "丶乓丷乓义") tt tt Eq.refl
wn00076 : Base 3 → ⟪ (ℓ "丨並") ⟫ʷ ≈ ⟪ (ℓ "並丷") ⟫ʷ
wn00076 b = lw3 b (ℓ "丨並") (ℓ "並丷") tt tt Eq.refl
wn00077 : Base 3 → ⟪ (ℓ "义丷") ⟫ʷ ≈ ⟪ (ℓ "丷义") ⟫ʷ
wn00077 b = lw0 b (ℓ "义丷") (ℓ "丷义") tt tt Eq.refl
wn00078 : Base 3 → ⟪ (ℓ "乖丼") ⟫ʷ ≈ ⟪ (ℓ "丼乓") ⟫ʷ
wn00078 b = lw0 b (ℓ "乖丼") (ℓ "丼乓") tt tt Eq.refl
wn00079 : Base 3 → ⟪ (ℓ "丷丨") ⟫ʷ ≈ ⟪ (ℓ "丨丷") ⟫ʷ
wn00079 b = lw3 b (ℓ "丷丨") (ℓ "丨丷") tt tt Eq.refl
wn00080 : Base 3 → ⟪ (ℓ "丶丨") ⟫ʷ ≈ ⟪ (ℓ "丨丶") ⟫ʷ
wn00080 b = lw3 b (ℓ "丶丨") (ℓ "丨丶") tt tt Eq.refl
wn00081 : Base 3 → ⟪ (ℓ "丶乓丷乓义") ⟫ʷ ≈ ⟪ (ℓ "乜") ⟫ʷ
wn00081 b = lw0 b (ℓ "丶乓丷乓义") (ℓ "乜") tt tt Eq.refl
wn00082 : Base 3 → ⟪ (ℓ "义举") ⟫ʷ ≈ ⟪ (ℓ "举义") ⟫ʷ
wn00082 b = lw0 b (ℓ "义举") (ℓ "举义") tt tt Eq.refl
wn00083 : Base 3 → ⟪ (ℓ "乆丨") ⟫ʷ ≈ ⟪ (ℓ "丨乆") ⟫ʷ
wn00083 b = lw3 b (ℓ "乆丨") (ℓ "丨乆") tt tt Eq.refl
wn00084 : Base 3 → ⟪ (ℓ "举丼") ⟫ʷ ≈ ⟪ (ℓ "丼乊") ⟫ʷ
wn00084 b = lw0 b (ℓ "举丼") (ℓ "丼乊") tt tt Eq.refl
wn00085 : Base 3 → ⟪ (ℓ "乙") ⟫ʷ ≈ ⟪ (ℓ "丠乆両乆丧") ⟫ʷ
wn00085 b = lw3 b (ℓ "乙") (ℓ "丠乆両乆丧") tt tt Eq.refl
wn00086 : Base 3 → ⟪ (ℓ "丶举") ⟫ʷ ≈ ⟪ (ℓ "举丶") ⟫ʷ
wn00086 b = lw0 b (ℓ "丶举") (ℓ "举丶") tt tt Eq.refl
wn00087 : Base 3 → ⟪ (ℓ "両丨") ⟫ʷ ≈ ⟪ (ℓ "丨両") ⟫ʷ
wn00087 b = lw3 b (ℓ "両丨") (ℓ "丨両") tt tt Eq.refl
wn00088 : Base 3 → ⟪ (ℓ "丠丨") ⟫ʷ ≈ ⟪ (ℓ "丨丠") ⟫ʷ
wn00088 b = lw3 b (ℓ "丠丨") (ℓ "丨丠") tt tt Eq.refl
wn00089 : Base 3 → ⟪ (ℓ "丠乆両乆丧") ⟫ʷ ≈ ⟪ (ℓ "乙") ⟫ʷ
wn00089 b = lw3 b (ℓ "丠乆両乆丧") (ℓ "乙") tt tt Eq.refl
wn00090 : Base 3 → ⟪ (ℓ "丶九") ⟫ʷ ≈ ⟪ (ℓ "九丶") ⟫ʷ
wn00090 b = lw3 b (ℓ "丶九") (ℓ "九丶") tt tt Eq.refl
wn00091 : Base 3 → ⟪ (ℓ "义丽") ⟫ʷ ≈ ⟪ (ℓ "丽义") ⟫ʷ
wn00091 b = lw0 b (ℓ "义丽") (ℓ "丽义") tt tt Eq.refl
wn00092 : Base 3 → ⟪ (ℓ "乆丧") ⟫ʷ ≈ ⟪ (ℓ "丧乆") ⟫ʷ
wn00092 b = lw3 b (ℓ "乆丧") (ℓ "丧乆") tt tt Eq.refl
wn00093 : Base 3 → ⟪ (ℓ "丶丽") ⟫ʷ ≈ ⟪ (ℓ "丽丶") ⟫ʷ
wn00093 b = lw0 b (ℓ "丶丽") (ℓ "丽丶") tt tt Eq.refl
wn00094 : Base 3 → ⟪ (ℓ "両丧") ⟫ʷ ≈ ⟪ (ℓ "丧両") ⟫ʷ
wn00094 b = lw3 b (ℓ "両丧") (ℓ "丧両") tt tt Eq.refl
wn00095 : Base 3 → ⟪ (ℓ "丠丧") ⟫ʷ ≈ ⟪ (ℓ "丧丠") ⟫ʷ
wn00095 b = lw3 b (ℓ "丠丧") (ℓ "丧丠") tt tt Eq.refl
wn00096 : Base 3 → ⟪ (ℓ "丿丼") ⟫ʷ ≈ ⟪ (ℓ "丼之") ⟫ʷ
wn00096 b = lw0 b (ℓ "丿丼") (ℓ "丼之") tt tt Eq.refl
wn00097 : Base 3 → ⟪ (ℓ "之丼") ⟫ʷ ≈ ⟪ (ℓ "丼丿") ⟫ʷ
wn00097 b = lw0 b (ℓ "之丼") (ℓ "丼丿") tt tt Eq.refl
wn00098 : Base 3 → ⟪ (ℓ "丿丹") ⟫ʷ ≈ ⟪ (ℓ "丹丿") ⟫ʷ
wn00098 b = lw0 b (ℓ "丿丹") (ℓ "丹丿") tt tt Eq.refl
wn00099 : Base 3 → ⟪ (ℓ "丸丠") ⟫ʷ ≈ ⟪ (ℓ "丠丸") ⟫ʷ
wn00099 b = lw3 b (ℓ "丸丠") (ℓ "丠丸") tt tt Eq.refl
wn00100 : Base 3 → ⟪ (ℓ "乙") ⟫ʷ ≈ ⟪ (ℓ "丠乃両乃丶") ⟫ʷ
wn00100 b = lw3 b (ℓ "乙") (ℓ "丠乃両乃丶") tt tt Eq.refl
wn00101 : Base 3 → ⟪ (ℓ "丽丶") ⟫ʷ ≈ ⟪ (ℓ "丶丽") ⟫ʷ
wn00101 b = lw0 b (ℓ "丽丶") (ℓ "丶丽") tt tt Eq.refl
wn00102 : Base 3 → ⟪ (ℓ "両丶") ⟫ʷ ≈ ⟪ (ℓ "丶両") ⟫ʷ
wn00102 b = lw3 b (ℓ "両丶") (ℓ "丶両") tt tt Eq.refl
wn00103 : Base 3 → ⟪ (ℓ "丠丶") ⟫ʷ ≈ ⟪ (ℓ "丶丠") ⟫ʷ
wn00103 b = lw3 b (ℓ "丠丶") (ℓ "丶丠") tt tt Eq.refl
wn00104 : Base 3 → ⟪ (ℓ "丠乃両乃丶") ⟫ʷ ≈ ⟪ (ℓ "乙") ⟫ʷ
wn00104 b = lw3 b (ℓ "丠乃両乃丶") (ℓ "乙") tt tt Eq.refl
wn00105 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "乖乖") ⟫ʷ
wn00105 b = lw0 b [] (ℓ "乖乖") tt tt Eq.refl
wn00106 : Base 3 → ⟪ (ℓ "丶丿") ⟫ʷ ≈ ⟪ (ℓ "丿丶") ⟫ʷ
wn00106 b = lw0 b (ℓ "丶丿") (ℓ "丿丶") tt tt Eq.refl
wn00107 : Base 3 → ⟪ (ℓ "丼丿") ⟫ʷ ≈ ⟪ (ℓ "之丼") ⟫ʷ
wn00107 b = lw0 b (ℓ "丼丿") (ℓ "之丼") tt tt Eq.refl
wn00108 : Base 3 → ⟪ (ℓ "丼之") ⟫ʷ ≈ ⟪ (ℓ "丿丼") ⟫ʷ
wn00108 b = lw0 b (ℓ "丼之") (ℓ "丿丼") tt tt Eq.refl
wn00109 : Base 3 → ⟪ (ℓ "両丸") ⟫ʷ ≈ ⟪ (ℓ "丸両") ⟫ʷ
wn00109 b = lw3 b (ℓ "両丸") (ℓ "丸両") tt tt Eq.refl
wn00110 : Base 3 → ⟪ (ℓ "丠丸") ⟫ʷ ≈ ⟪ (ℓ "丸丠") ⟫ʷ
wn00110 b = lw3 b (ℓ "丠丸") (ℓ "丸丠") tt tt Eq.refl
wn00111 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "乓乓") ⟫ʷ
wn00111 b = lw0 b [] (ℓ "乓乓") tt tt Eq.refl
wn00112 : Base 3 → ⟪ (ℓ "乃乆") ⟫ʷ ≈ ⟪ (ℓ "乆乃") ⟫ʷ
wn00112 b = lw3 b (ℓ "乃乆") (ℓ "乆乃") tt tt Eq.refl
wn00113 : Base 3 → ⟪ (ℓ "丼乓") ⟫ʷ ≈ ⟪ (ℓ "乖丼") ⟫ʷ
wn00113 b = lw0 b (ℓ "丼乓") (ℓ "乖丼") tt tt Eq.refl
wn00114 : Base 3 → ⟪ (ℓ "丼乖") ⟫ʷ ≈ ⟪ (ℓ "乓丼") ⟫ʷ
wn00114 b = lw0 b (ℓ "丼乖") (ℓ "乓丼") tt tt Eq.refl
wn00115 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "乀乀") ⟫ʷ
wn00115 b = lw0 b [] (ℓ "乀乀") tt tt Eq.refl
wn00116 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "上下") ⟫ʷ
wn00116 b = lw3 b [] (ℓ "上下") tt tt Eq.refl
wn00117 : Base 3 → ⟪ (ℓ "下临上") ⟫ʷ ≈ ⟪ (ℓ "临") ⟫ʷ
wn00117 b = lw3 b (ℓ "下临上") (ℓ "临") tt tt Eq.refl
wn00118 : Base 3 → ⟪ (ℓ "上並") ⟫ʷ ≈ ⟪ (ℓ "並丐") ⟫ʷ
wn00118 b = lw3 b (ℓ "上並") (ℓ "並丐") tt tt Eq.refl
wn00119 : Base 3 → ⟪ (ℓ "下並") ⟫ʷ ≈ ⟪ (ℓ "並丑") ⟫ʷ
wn00119 b = lw3 b (ℓ "下並") (ℓ "並丑") tt tt Eq.refl
wn00120 : Base 3 → ⟪ (ℓ "丑乜丐") ⟫ʷ ≈ ⟪ (ℓ "乢") ⟫ʷ
wn00120 b = lw0 b (ℓ "丑乜丐") (ℓ "乢") tt tt Eq.refl
wn00121 : Base 3 → ⟪ (ℓ "並丐") ⟫ʷ ≈ ⟪ (ℓ "上並") ⟫ʷ
wn00121 b = lw3 b (ℓ "並丐") (ℓ "上並") tt tt Eq.refl
wn00122 : Base 3 → ⟪ (ℓ "並丁") ⟫ʷ ≈ ⟪ (ℓ "一並") ⟫ʷ
wn00122 b = lw3 b (ℓ "並丁") (ℓ "一並") tt tt Eq.refl
wn00123 : Base 3 → ⟪ (ℓ "並上") ⟫ʷ ≈ ⟪ (ℓ "丐並") ⟫ʷ
wn00123 b = lw3 b (ℓ "並上") (ℓ "丐並") tt tt Eq.refl
wn00124 : Base 3 → ⟪ (ℓ "並一") ⟫ʷ ≈ ⟪ (ℓ "丁並") ⟫ʷ
wn00124 b = lw3 b (ℓ "並一") (ℓ "丁並") tt tt Eq.refl
wn00125 : Base 3 → ⟪ (ℓ "丐义丹乊丹丽丐丁") ⟫ʷ ≈ ⟪ (ℓ "丐义丹乊丹丽丐丁") ⟫ʷ
wn00125 b = lw0 b (ℓ "丐义丹乊丹丽丐丁") (ℓ "丐义丹乊丹丽丐丁") tt tt Eq.refl
wn00126 : Base 3 → ⟪ (ℓ "下丵上") ⟫ʷ ≈ ⟪ (ℓ "丵") ⟫ʷ
wn00126 b = lw3 b (ℓ "下丵上") (ℓ "丵") tt tt Eq.refl
wn00127 : Base 3 → ⟪ (ℓ "一並") ⟫ʷ ≈ ⟪ (ℓ "並丁") ⟫ʷ
wn00127 b = lw3 b (ℓ "一並") (ℓ "並丁") tt tt Eq.refl
wn00128 : Base 3 → ⟪ (ℓ "乢") ⟫ʷ ≈ ⟪ (ℓ "丐乜丑") ⟫ʷ
wn00128 b = lw0 b (ℓ "乢") (ℓ "丐乜丑") tt tt Eq.refl
wn00129 : Base 3 → ⟪ (ℓ "並丑") ⟫ʷ ≈ ⟪ (ℓ "下並") ⟫ʷ
wn00129 b = lw3 b (ℓ "並丑") (ℓ "下並") tt tt Eq.refl
wn00130 : Base 3 → ⟪ (ℓ "丼义丼") ⟫ʷ ≈ ⟪ (ℓ "丽") ⟫ʷ
wn00130 b = lw0 b (ℓ "丼义丼") (ℓ "丽") tt tt Eq.refl
wn00131 : Base 3 → ⟪ (ℓ "丼丨丼") ⟫ʷ ≈ ⟪ (ℓ "両") ⟫ʷ
wn00131 b = lw3 b (ℓ "丼丨丼") (ℓ "両") tt tt Eq.refl
wn00132 : Base 3 → ⟪ (ℓ "丼丧丼") ⟫ʷ ≈ ⟪ (ℓ "丠") ⟫ʷ
wn00132 b = lw3 b (ℓ "丼丧丼") (ℓ "丠") tt tt Eq.refl
wn00133 : Base 3 → ⟪ (ℓ "丼丵丼") ⟫ʷ ≈ ⟪ (ℓ "久") ⟫ʷ
wn00133 b = lw3 b (ℓ "丼丵丼") (ℓ "久") tt tt Eq.refl
wn00134 : Base 3 → ⟪ (ℓ "丼临丼") ⟫ʷ ≈ ⟪ (ℓ "乄") ⟫ʷ
wn00134 b = lw3 b (ℓ "丼临丼") (ℓ "乄") tt tt Eq.refl
wn00135 : Base 3 → ⟪ (ℓ "乏丽乏") ⟫ʷ ≈ ⟪ (ℓ "丶") ⟫ʷ
wn00135 b = lw0 b (ℓ "乏丽乏") (ℓ "丶") tt tt Eq.refl
wn00136 : Base 3 → ⟪ (ℓ "乏乓乏") ⟫ʷ ≈ ⟪ (ℓ "乆") ⟫ʷ
wn00136 b = lw0 b (ℓ "乏乓乏") (ℓ "乆") tt tt Eq.refl
wn00137 : Base 3 → ⟪ (ℓ "久並") ⟫ʷ ≈ ⟪ (ℓ "並么") ⟫ʷ
wn00137 b = lw3 b (ℓ "久並") (ℓ "並么") tt tt Eq.refl
wn00138 : Base 3 → ⟪ (ℓ "乏么乏") ⟫ʷ ≈ ⟪ (ℓ "乕") ⟫ʷ
wn00138 b = lw0 b (ℓ "乏么乏") (ℓ "乕") tt tt Eq.refl
wn00139 : Base 3 → ⟪ (ℓ "並么") ⟫ʷ ≈ ⟪ (ℓ "久並") ⟫ʷ
wn00139 b = lw3 b (ℓ "並么") (ℓ "久並") tt tt Eq.refl
wn00140 : Base 3 → ⟪ (ℓ "乄並") ⟫ʷ ≈ ⟪ (ℓ "並乇") ⟫ʷ
wn00140 b = lw3 b (ℓ "乄並") (ℓ "並乇") tt tt Eq.refl
wn00141 : Base 3 → ⟪ (ℓ "乏乇乏") ⟫ʷ ≈ ⟪ (ℓ "乔") ⟫ʷ
wn00141 b = lw0 b (ℓ "乏乇乏") (ℓ "乔") tt tt Eq.refl
wn00142 : Base 3 → ⟪ (ℓ "並乇") ⟫ʷ ≈ ⟪ (ℓ "乄並") ⟫ʷ
wn00142 b = lw3 b (ℓ "並乇") (ℓ "乄並") tt tt Eq.refl
wn00143 : Base 3 → ⟪ (ℓ "丼丶丼") ⟫ʷ ≈ ⟪ (ℓ "丶") ⟫ʷ
wn00143 b = lw3 b (ℓ "丼丶丼") (ℓ "丶") tt tt Eq.refl
wn00144 : Base 3 → ⟪ (ℓ "丼乃丼") ⟫ʷ ≈ ⟪ (ℓ "丳") ⟫ʷ
wn00144 b = lw3 b (ℓ "丼乃丼") (ℓ "丳") tt tt Eq.refl
wn00145 : Base 3 → ⟪ (ℓ "丼両丼") ⟫ʷ ≈ ⟪ (ℓ "丨") ⟫ʷ
wn00145 b = lw3 b (ℓ "丼両丼") (ℓ "丨") tt tt Eq.refl
wn00146 : Base 3 → ⟪ (ℓ "丼丠丼") ⟫ʷ ≈ ⟪ (ℓ "丧") ⟫ʷ
wn00146 b = lw3 b (ℓ "丼丠丼") (ℓ "丧") tt tt Eq.refl
wn00147 : Base 3 → ⟪ (ℓ "丧丳丨丳丶") ⟫ʷ ≈ ⟪ (ℓ "乙") ⟫ʷ
wn00147 b = lw3 b (ℓ "丧丳丨丳丶") (ℓ "乙") tt tt Eq.refl
wn00148 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "下三上下丈上") ⟫ʷ
wn00148 b = lw3 b [] (ℓ "下三上下丈上") tt tt Eq.refl
wn00149 : Base 3 → ⟪ (ℓ "下丈上九下三上") ⟫ʷ ≈ ⟪ (ℓ "九") ⟫ʷ
wn00149 b = lw3 b (ℓ "下丈上九下三上") (ℓ "九") tt tt Eq.refl
wn00150 : Base 3 → ⟪ (ℓ "下丈上丧下三上") ⟫ʷ ≈ ⟪ (ℓ "乄乃且") ⟫ʷ
wn00150 b = lw3 b (ℓ "下丈上丧下三上") (ℓ "乄乃且") tt tt Eq.refl
wn00151 : Base 3 → ⟪ (ℓ "乏且") ⟫ʷ ≈ ⟪ (ℓ "业乏") ⟫ʷ
wn00151 b = lw0 b (ℓ "乏且") (ℓ "业乏") tt tt Eq.refl
wn00152 : Base 3 → ⟪ (ℓ "下丈上丨下三上") ⟫ʷ ≈ ⟪ (ℓ "丕乃久") ⟫ʷ
wn00152 b = lw3 b (ℓ "下丈上丨下三上") (ℓ "丕乃久") tt tt Eq.refl
wn00153 : Base 3 → ⟪ (ℓ "乏丕") ⟫ʷ ≈ ⟪ (ℓ "丛乏") ⟫ʷ
wn00153 b = lw0 b (ℓ "乏丕") (ℓ "丛乏") tt tt Eq.refl
wn00154 : Base 3 → ⟪ (ℓ "业丛") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00154 b = lw0 b (ℓ "业丛") [] tt tt Eq.refl
wn00155 : Base 3 → ⟪ (ℓ "九") ⟫ʷ ≈ ⟪ (ℓ "久丧乄丹久丨乄丹丵丠临") ⟫ʷ
wn00155 b = lw3 b (ℓ "九") (ℓ "久丧乄丹久丨乄丹丵丠临") tt tt Eq.refl
wn00156 : Base 3 → ⟪ (ℓ "乓么丶乇") ⟫ʷ ≈ ⟪ (ℓ "么丶乇乓") ⟫ʷ
wn00156 b = lw0 b (ℓ "乓么丶乇") (ℓ "么丶乇乓") tt tt Eq.refl
wn00157 : Base 3 → ⟪ (ℓ "丼乀") ⟫ʷ ≈ ⟪ (ℓ "乌丼") ⟫ʷ
wn00157 b = lw0 b (ℓ "丼乀") (ℓ "乌丼") tt tt Eq.refl
wn00158 : Base 3 → ⟪ (ℓ "丼乌") ⟫ʷ ≈ ⟪ (ℓ "乀丼") ⟫ʷ
wn00158 b = lw0 b (ℓ "丼乌") (ℓ "乀丼") tt tt Eq.refl
wn00159 : Base 3 → ⟪ (ℓ "乓么丷乇") ⟫ʷ ≈ ⟪ (ℓ "么丷乇乓") ⟫ʷ
wn00159 b = lw0 b (ℓ "乓么丷乇") (ℓ "么丷乇乓") tt tt Eq.refl
wn00160 : Base 3 → ⟪ (ℓ "乃丵丠临") ⟫ʷ ≈ ⟪ (ℓ "丵丠临乃") ⟫ʷ
wn00160 b = lw3 b (ℓ "乃丵丠临") (ℓ "丵丠临乃") tt tt Eq.refl
wn00161 : Base 3 → ⟪ (ℓ "乃乃") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00161 b = lw3 b (ℓ "乃乃") [] tt tt Eq.refl
wn00162 : Base 3 → ⟪ (ℓ "久丧乄丹久丨乄丹丵丠临") ⟫ʷ ≈ ⟪ (ℓ "九") ⟫ʷ
wn00162 b = lw3 b (ℓ "久丧乄丹久丨乄丹丵丠临") (ℓ "九") tt tt Eq.refl
wn00163 : Base 3 → ⟪ (ℓ "乜") ⟫ʷ ≈ ⟪ (ℓ "丶乖丷乖丽") ⟫ʷ
wn00163 b = lw0 b (ℓ "乜") (ℓ "丶乖丷乖丽") tt tt Eq.refl
wn00164 : Base 3 → ⟪ (ℓ "丢丧") ⟫ʷ ≈ ⟪ (ℓ "丧丢") ⟫ʷ
wn00164 b = lw3 b (ℓ "丢丧") (ℓ "丧丢") tt tt Eq.refl
wn00165 : Base 3 → ⟪ (ℓ "丢丨") ⟫ʷ ≈ ⟪ (ℓ "丨丢") ⟫ʷ
wn00165 b = lw3 b (ℓ "丢丨") (ℓ "丨丢") tt tt Eq.refl
wn00166 : Base 3 → ⟪ (ℓ "丶乖丷乖丽") ⟫ʷ ≈ ⟪ (ℓ "乜") ⟫ʷ
wn00166 b = lw0 b (ℓ "丶乖丷乖丽") (ℓ "乜") tt tt Eq.refl
wn00167 : Base 3 → ⟪ (ℓ "丢丶") ⟫ʷ ≈ ⟪ (ℓ "丶丢") ⟫ʷ
wn00167 b = lw3 b (ℓ "丢丶") (ℓ "丶丢") tt tt Eq.refl
wn00168 : Base 3 → ⟪ (ℓ "丢丷") ⟫ʷ ≈ ⟪ (ℓ "丷丢") ⟫ʷ
wn00168 b = lw3 b (ℓ "丢丷") (ℓ "丷丢") tt tt Eq.refl
wn00169 : Base 3 → ⟪ (ℓ "丶丵") ⟫ʷ ≈ ⟪ (ℓ "丵丶") ⟫ʷ
wn00169 b = lw3 b (ℓ "丶丵") (ℓ "丵丶") tt tt Eq.refl
wn00170 : Base 3 → ⟪ (ℓ "丷丵") ⟫ʷ ≈ ⟪ (ℓ "丵丷") ⟫ʷ
wn00170 b = lw3 b (ℓ "丷丵") (ℓ "丵丷") tt tt Eq.refl
wn00171 : Base 3 → ⟪ (ℓ "丼九丼") ⟫ʷ ≈ ⟪ (ℓ "九") ⟫ʷ
wn00171 b = lw3 b (ℓ "丼九丼") (ℓ "九") tt tt Eq.refl
wn00172 : Base 3 → ⟪ (ℓ "乙丢") ⟫ʷ ≈ ⟪ (ℓ "丢乙") ⟫ʷ
wn00172 b = lw3 b (ℓ "乙丢") (ℓ "丢乙") tt tt Eq.refl
wn00173 : Base 3 → ⟪ (ℓ "丞乏") ⟫ʷ ≈ ⟪ (ℓ "乏丘") ⟫ʷ
wn00173 b = lw0 b (ℓ "丞乏") (ℓ "乏丘") tt tt Eq.refl
wn00174 : Base 3 → ⟪ (ℓ "丧丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丘九丘丧") ⟫ʷ
wn00174 b = lw3 b (ℓ "丧丘九丘") (ℓ "丘九丘丧") tt tt Eq.refl
wn00175 : Base 3 → ⟪ (ℓ "乏丘") ⟫ʷ ≈ ⟪ (ℓ "丞乏") ⟫ʷ
wn00175 b = lw0 b (ℓ "乏丘") (ℓ "丞乏") tt tt Eq.refl
wn00176 : Base 3 → ⟪ (ℓ "丨丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丘九丘丨") ⟫ʷ
wn00176 b = lw3 b (ℓ "丨丘九丘") (ℓ "丘九丘丨") tt tt Eq.refl
wn00177 : Base 3 → ⟪ (ℓ "乙丶") ⟫ʷ ≈ ⟪ (ℓ "丶乙") ⟫ʷ
wn00177 b = lw3 b (ℓ "乙丶") (ℓ "丶乙") tt tt Eq.refl
wn00178 : Base 3 → ⟪ (ℓ "乙丸") ⟫ʷ ≈ ⟪ (ℓ "丸乙") ⟫ʷ
wn00178 b = lw3 b (ℓ "乙丸") (ℓ "丸乙") tt tt Eq.refl
wn00179 : Base 3 → ⟪ (ℓ "丷丽") ⟫ʷ ≈ ⟪ (ℓ "丽丷") ⟫ʷ
wn00179 b = lw0 b (ℓ "丷丽") (ℓ "丽丷") tt tt Eq.refl
wn00180 : Base 3 → ⟪ (ℓ "乙丷") ⟫ʷ ≈ ⟪ (ℓ "丷乙") ⟫ʷ
wn00180 b = lw3 b (ℓ "乙丷") (ℓ "丷乙") tt tt Eq.refl
wn00181 : Base 3 → ⟪ (ℓ "丷举") ⟫ʷ ≈ ⟪ (ℓ "举丷") ⟫ʷ
wn00181 b = lw0 b (ℓ "丷举") (ℓ "举丷") tt tt Eq.refl
wn00182 : Base 3 → ⟪ (ℓ "九丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丘九丘九") ⟫ʷ
wn00182 b = lw3 b (ℓ "九丘九丘") (ℓ "丘九丘九") tt tt Eq.refl
wn00183 : Base 3 → ⟪ (ℓ "丈丧") ⟫ʷ ≈ ⟪ (ℓ "丧丈") ⟫ʷ
wn00183 b = lw3 b (ℓ "丈丧") (ℓ "丧丈") tt tt Eq.refl
wn00184 : Base 3 → ⟪ (ℓ "丈丨") ⟫ʷ ≈ ⟪ (ℓ "丨丈") ⟫ʷ
wn00184 b = lw3 b (ℓ "丈丨") (ℓ "丨丈") tt tt Eq.refl
wn00185 : Base 3 → ⟪ (ℓ "三丧") ⟫ʷ ≈ ⟪ (ℓ "丧三") ⟫ʷ
wn00185 b = lw3 b (ℓ "三丧") (ℓ "丧三") tt tt Eq.refl
wn00186 : Base 3 → ⟪ (ℓ "三丨") ⟫ʷ ≈ ⟪ (ℓ "丨三") ⟫ʷ
wn00186 b = lw3 b (ℓ "三丨") (ℓ "丨三") tt tt Eq.refl
wn00187 : Base 3 → ⟪ (ℓ "九丒丘九丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘九丒丘九") ⟫ʷ
wn00187 b = lw3 b (ℓ "九丒丘九丒丘") (ℓ "丒丘九丒丘九") tt tt Eq.refl
wn00188 : Base 3 → ⟪ (ℓ "乙不") ⟫ʷ ≈ ⟪ (ℓ "不乙") ⟫ʷ
wn00188 b = lw3 b (ℓ "乙不") (ℓ "不乙") tt tt Eq.refl
wn00189 : Base 3 → ⟪ (ℓ "丩並") ⟫ʷ ≈ ⟪ (ℓ "並丸") ⟫ʷ
wn00189 b = lw3 b (ℓ "丩並") (ℓ "並丸") tt tt Eq.refl
wn00190 : Base 3 → ⟪ (ℓ "丽丸") ⟫ʷ ≈ ⟪ (ℓ "丸丽") ⟫ʷ
wn00190 b = lw0 b (ℓ "丽丸") (ℓ "丸丽") tt tt Eq.refl
wn00191 : Base 3 → ⟪ (ℓ "並丸") ⟫ʷ ≈ ⟪ (ℓ "丩並") ⟫ʷ
wn00191 b = lw3 b (ℓ "並丸") (ℓ "丩並") tt tt Eq.refl
wn00192 : Base 3 → ⟪ (ℓ "両丩") ⟫ʷ ≈ ⟪ (ℓ "丩両") ⟫ʷ
wn00192 b = lw3 b (ℓ "両丩") (ℓ "丩両") tt tt Eq.refl
wn00193 : Base 3 → ⟪ (ℓ "丠丩") ⟫ʷ ≈ ⟪ (ℓ "丩丠") ⟫ʷ
wn00193 b = lw3 b (ℓ "丠丩") (ℓ "丩丠") tt tt Eq.refl
wn00194 : Base 3 → ⟪ (ℓ "丧丒丘九丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘九丒丘丧") ⟫ʷ
wn00194 b = lw3 b (ℓ "丧丒丘九丒丘") (ℓ "丒丘九丒丘丧") tt tt Eq.refl
wn00195 : Base 3 → ⟪ (ℓ "丨丒丘九丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘九丒丘丨") ⟫ʷ
wn00195 b = lw3 b (ℓ "丨丒丘九丒丘") (ℓ "丒丘九丒丘丨") tt tt Eq.refl
wn00196 : Base 3 → ⟪ (ℓ "丐丶丣丷丣丧丐一") ⟫ʷ ≈ ⟪ (ℓ "丐丶丣丷丣丧丐一") ⟫ʷ
wn00196 b = lw3 b (ℓ "丐丶丣丷丣丧丐一") (ℓ "丐丶丣丷丣丧丐一") tt tt Eq.refl
wn00197 : Base 3 → ⟪ (ℓ "习丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丘九丘习") ⟫ʷ
wn00197 b = lw3 b (ℓ "习丘九丘") (ℓ "丘九丘习") tt tt Eq.refl
wn00198 : Base 3 → ⟪ (ℓ "丽丷") ⟫ʷ ≈ ⟪ (ℓ "丷丽") ⟫ʷ
wn00198 b = lw0 b (ℓ "丽丷") (ℓ "丷丽") tt tt Eq.refl
wn00199 : Base 3 → ⟪ (ℓ "両丷") ⟫ʷ ≈ ⟪ (ℓ "丷両") ⟫ʷ
wn00199 b = lw3 b (ℓ "両丷") (ℓ "丷両") tt tt Eq.refl
wn00200 : Base 3 → ⟪ (ℓ "丠丷") ⟫ʷ ≈ ⟪ (ℓ "丷丠") ⟫ʷ
wn00200 b = lw3 b (ℓ "丠丷") (ℓ "丷丠") tt tt Eq.refl
wn00201 : Base 3 → ⟪ (ℓ "习丈") ⟫ʷ ≈ ⟪ (ℓ "丈习") ⟫ʷ
wn00201 b = lw3 b (ℓ "习丈") (ℓ "丈习") tt tt Eq.refl
wn00202 : Base 3 → ⟪ (ℓ "习三") ⟫ʷ ≈ ⟪ (ℓ "三习") ⟫ʷ
wn00202 b = lw3 b (ℓ "习三") (ℓ "三习") tt tt Eq.refl
wn00203 : Base 3 → ⟪ (ℓ "丶丈") ⟫ʷ ≈ ⟪ (ℓ "丈丶") ⟫ʷ
wn00203 b = lw3 b (ℓ "丶丈") (ℓ "丈丶") tt tt Eq.refl
wn00204 : Base 3 → ⟪ (ℓ "丶三") ⟫ʷ ≈ ⟪ (ℓ "三丶") ⟫ʷ
wn00204 b = lw3 b (ℓ "丶三") (ℓ "三丶") tt tt Eq.refl
wn00205 : Base 3 → ⟪ (ℓ "丶丧") ⟫ʷ ≈ ⟪ (ℓ "丧丶") ⟫ʷ
wn00205 b = lw3 b (ℓ "丶丧") (ℓ "丧丶") tt tt Eq.refl
wn00206 : Base 3 → ⟪ (ℓ "丷丈") ⟫ʷ ≈ ⟪ (ℓ "丈丷") ⟫ʷ
wn00206 b = lw3 b (ℓ "丷丈") (ℓ "丈丷") tt tt Eq.refl
wn00207 : Base 3 → ⟪ (ℓ "丷三") ⟫ʷ ≈ ⟪ (ℓ "三丷") ⟫ʷ
wn00207 b = lw3 b (ℓ "丷三") (ℓ "三丷") tt tt Eq.refl
wn00208 : Base 3 → ⟪ (ℓ "丷丧") ⟫ʷ ≈ ⟪ (ℓ "丧丷") ⟫ʷ
wn00208 b = lw3 b (ℓ "丷丧") (ℓ "丧丷") tt tt Eq.refl
wn00209 : Base 3 → ⟪ (ℓ "习丒丘九丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘九丒丘习") ⟫ʷ
wn00209 b = lw3 b (ℓ "习丒丘九丒丘") (ℓ "丒丘九丒丘习") tt tt Eq.refl
wn00210 : Base 3 → ⟪ (ℓ "且丽") ⟫ʷ ≈ ⟪ (ℓ "丽且") ⟫ʷ
wn00210 b = lw0 b (ℓ "且丽") (ℓ "丽且") tt tt Eq.refl
wn00211 : Base 3 → ⟪ (ℓ "且举") ⟫ʷ ≈ ⟪ (ℓ "举且") ⟫ʷ
wn00211 b = lw0 b (ℓ "且举") (ℓ "举且") tt tt Eq.refl
wn00212 : Base 3 → ⟪ (ℓ "丕丽") ⟫ʷ ≈ ⟪ (ℓ "丽丕") ⟫ʷ
wn00212 b = lw0 b (ℓ "丕丽") (ℓ "丽丕") tt tt Eq.refl
wn00213 : Base 3 → ⟪ (ℓ "丕举") ⟫ʷ ≈ ⟪ (ℓ "举丕") ⟫ʷ
wn00213 b = lw0 b (ℓ "丕举") (ℓ "举丕") tt tt Eq.refl
wn00214 : Base 3 → ⟪ (ℓ "乙三") ⟫ʷ ≈ ⟪ (ℓ "三乙") ⟫ʷ
wn00214 b = lw3 b (ℓ "乙三") (ℓ "三乙") tt tt Eq.refl
wn00215 : Base 3 → ⟪ (ℓ "丘丼") ⟫ʷ ≈ ⟪ (ℓ "丼丒") ⟫ʷ
wn00215 b = lw3 b (ℓ "丘丼") (ℓ "丼丒") tt tt Eq.refl
