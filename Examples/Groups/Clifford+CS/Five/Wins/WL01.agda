------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WL01 where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

wl0001 : Base 4 → ⟪ (ℓ "丶乊") ⟫ʷ ≈ ⟪ (ℓ "乊丶") ⟫ʷ
wl0001 c4 = lw4 c4 (ℓ "丶乊") (ℓ "乊丶") tt tt Eq.refl

wl0002 : Base 4 → ⟪ (ℓ "乥乼乥") ⟫ʷ ≈ ⟪ (ℓ "乼乥乼") ⟫ʷ
wl0002 c4 = lw0 c4 (ℓ "乥乼乥") (ℓ "乼乥乼") tt tt Eq.refl

wl0003 : Base 4 → ⟪ (ℓ "乥乥") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0003 c4 = lw4 c4 (ℓ "乥乥") [] tt tt Eq.refl

wl0004 : Base 4 → ⟪ (ℓ "乼乼") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0004 c4 = lw0 c4 (ℓ "乼乼") [] tt tt Eq.refl

wl0005 : Base 4 → ⟪ (ℓ "乩乊") ⟫ʷ ≈ ⟪ (ℓ "乊乕") ⟫ʷ
wl0005 c4 = lw0 c4 (ℓ "乩乊") (ℓ "乊乕") tt tt Eq.refl

wl0006 : Base 4 → ⟪ (ℓ "乊乊") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0006 c4 = lw4 c4 (ℓ "乊乊") [] tt tt Eq.refl

wl0007 : Base 4 → ⟪ (ℓ "乪乊") ⟫ʷ ≈ ⟪ (ℓ "乊乖") ⟫ʷ
wl0007 c4 = lw0 c4 (ℓ "乪乊") (ℓ "乊乖") tt tt Eq.refl

wl0008 : Base 4 → ⟪ (ℓ "乹乥") ⟫ʷ ≈ ⟪ (ℓ "乥乩") ⟫ʷ
wl0008 c4 = lw0 c4 (ℓ "乹乥") (ℓ "乥乩") tt tt Eq.refl

wl0009 : Base 4 → ⟪ (ℓ "乺乥") ⟫ʷ ≈ ⟪ (ℓ "乥乪") ⟫ʷ
wl0009 c4 = lw0 c4 (ℓ "乺乥") (ℓ "乥乪") tt tt Eq.refl

wl0010 : Base 4 → ⟪ (ℓ "为乊") ⟫ʷ ≈ ⟪ (ℓ "乊为") ⟫ʷ
wl0010 c4 = lw4 c4 (ℓ "为乊") (ℓ "乊为") tt tt Eq.refl

wl0011 : Base 4 → ⟪ (ℓ "乩乥") ⟫ʷ ≈ ⟪ (ℓ "乥乹") ⟫ʷ
wl0011 c4 = lw0 c4 (ℓ "乩乥") (ℓ "乥乹") tt tt Eq.refl

wl0012 : Base 4 → ⟪ (ℓ "乪乥") ⟫ʷ ≈ ⟪ (ℓ "乥乺") ⟫ʷ
wl0012 c4 = lw0 c4 (ℓ "乪乥") (ℓ "乥乺") tt tt Eq.refl

wl0013 : Base 4 → ⟪ (ℓ "乕乊") ⟫ʷ ≈ ⟪ (ℓ "乊乩") ⟫ʷ
wl0013 c4 = lw0 c4 (ℓ "乕乊") (ℓ "乊乩") tt tt Eq.refl

wl0014 : Base 4 → ⟪ (ℓ "乖乊") ⟫ʷ ≈ ⟪ (ℓ "乊乪") ⟫ʷ
wl0014 c4 = lw0 c4 (ℓ "乖乊") (ℓ "乊乪") tt tt Eq.refl

wl0015 : Base 4 → ⟪ (ℓ "丶丫") ⟫ʷ ≈ ⟪ (ℓ "丫乎") ⟫ʷ
wl0015 c4 = lw4 c4 (ℓ "丶丫") (ℓ "丫乎") tt tt Eq.refl

wl0016 : Base 4 → ⟪ (ℓ "为丫") ⟫ʷ ≈ ⟪ (ℓ "丫乒") ⟫ʷ
wl0016 c4 = lw4 c4 (ℓ "为丫") (ℓ "丫乒") tt tt Eq.refl

wl0017 : Base 4 → ⟪ (ℓ "乕乥") ⟫ʷ ≈ ⟪ (ℓ "乥乕") ⟫ʷ
wl0017 c4 = lw0 c4 (ℓ "乕乥") (ℓ "乥乕") tt tt Eq.refl

wl0018 : Base 4 → ⟪ (ℓ "丫丫") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0018 c4 = lw4 c4 (ℓ "丫丫") [] tt tt Eq.refl

wl0019 : Base 4 → ⟪ (ℓ "乒乊") ⟫ʷ ≈ ⟪ (ℓ "乊书") ⟫ʷ
wl0019 c4 = lw4 c4 (ℓ "乒乊") (ℓ "乊书") tt tt Eq.refl

wl0020 : Base 4 → ⟪ (ℓ "乭乥") ⟫ʷ ≈ ⟪ (ℓ "乥乽") ⟫ʷ
wl0020 c4 = lw0 c4 (ℓ "乭乥") (ℓ "乥乽") tt tt Eq.refl

wl0021 : Base 4 → ⟪ (ℓ "乽乥") ⟫ʷ ≈ ⟪ (ℓ "乥乭") ⟫ʷ
wl0021 c4 = lw0 c4 (ℓ "乽乥") (ℓ "乥乭") tt tt Eq.refl

wl0022 : Base 4 → ⟪ (ℓ "书乊") ⟫ʷ ≈ ⟪ (ℓ "乊乒") ⟫ʷ
wl0022 c4 = lw4 c4 (ℓ "书乊") (ℓ "乊乒") tt tt Eq.refl

wl0023 : Base 4 → ⟪ (ℓ "丰丫") ⟫ʷ ≈ ⟪ (ℓ "丫么") ⟫ʷ
wl0023 c4 = lw4 c4 (ℓ "丰丫") (ℓ "丫么") tt tt Eq.refl

wl0024 : Base 4 → ⟪ (ℓ "丯丫") ⟫ʷ ≈ ⟪ (ℓ "丫乇") ⟫ʷ
wl0024 c4 = lw4 c4 (ℓ "丯丫") (ℓ "丫乇") tt tt Eq.refl

wl0025 : Base 4 → ⟪ (ℓ "丫一") ⟫ʷ ≈ ⟪ (ℓ "一丫") ⟫ʷ
wl0025 c4 = lw4 c4 (ℓ "丫一") (ℓ "一丫") tt tt Eq.refl

wl0026 : Base 4 → ⟪ (ℓ "丌丫") ⟫ʷ ≈ ⟪ (ℓ "丫丒") ⟫ʷ
wl0026 c4 = lw4 c4 (ℓ "丌丫") (ℓ "丫丒") tt tt Eq.refl

wl0027 : Base 4 → ⟪ (ℓ "丒乢之乣之乎丒一") ⟫ʷ ≈ ⟪ (ℓ "丒乢之乣之乎丒丂") ⟫ʷ
wl0027 c4 = lw4 c4 (ℓ "丒乢之乣之乎丒一") (ℓ "丒乢之乣之乎丒丂") tt tt Eq.refl

wl0028 : Base 4 → ⟪ (ℓ "乏乊") ⟫ʷ ≈ ⟪ (ℓ "乊乣") ⟫ʷ
wl0028 c4 = lw4 c4 (ℓ "乏乊") (ℓ "乊乣") tt tt Eq.refl

wl0029 : Base 4 → ⟪ (ℓ "乣乊") ⟫ʷ ≈ ⟪ (ℓ "乊乏") ⟫ʷ
wl0029 c4 = lw4 c4 (ℓ "乣乊") (ℓ "乊乏") tt tt Eq.refl

wl0030 : Base 4 → ⟪ (ℓ "亘丫") ⟫ʷ ≈ ⟪ (ℓ "丫交") ⟫ʷ
wl0030 c4 = lw4 c4 (ℓ "亘丫") (ℓ "丫交") tt tt Eq.refl

wl0031 : Base 4 → ⟪ (ℓ "丫亦") ⟫ʷ ≈ ⟪ (ℓ "亚丫") ⟫ʷ
wl0031 c4 = lw4 c4 (ℓ "丫亦") (ℓ "亚丫") tt tt Eq.refl

wl0032 : Base 4 → ⟪ (ℓ "乗乊") ⟫ʷ ≈ ⟪ (ℓ "乊乫") ⟫ʷ
wl0032 c4 = lw0 c4 (ℓ "乗乊") (ℓ "乊乫") tt tt Eq.refl

wl0033 : Base 4 → ⟪ (ℓ "乐乊") ⟫ʷ ≈ ⟪ (ℓ "乊乤") ⟫ʷ
wl0033 c4 = lw4 c4 (ℓ "乐乊") (ℓ "乊乤") tt tt Eq.refl

wl0034 : Base 4 → ⟪ (ℓ "乫乥") ⟫ʷ ≈ ⟪ (ℓ "乥乻") ⟫ʷ
wl0034 c4 = lw0 c4 (ℓ "乫乥") (ℓ "乥乻") tt tt Eq.refl

wl0035 : Base 4 → ⟪ (ℓ "乻乥") ⟫ʷ ≈ ⟪ (ℓ "乥乫") ⟫ʷ
wl0035 c4 = lw0 c4 (ℓ "乻乥") (ℓ "乥乫") tt tt Eq.refl

wl0036 : Base 4 → ⟪ (ℓ "乤乊") ⟫ʷ ≈ ⟪ (ℓ "乊乐") ⟫ʷ
wl0036 c4 = lw4 c4 (ℓ "乤乊") (ℓ "乊乐") tt tt Eq.refl

wl0037 : Base 4 → ⟪ (ℓ "京乊") ⟫ʷ ≈ ⟪ (ℓ "乊亰") ⟫ʷ
wl0037 c4 = lw0 c4 (ℓ "京乊") (ℓ "乊亰") tt tt Eq.refl

wl0038 : Base 4 → ⟪ (ℓ "乊亲") ⟫ʷ ≈ ⟪ (ℓ "亮乊") ⟫ʷ
wl0038 c4 = lw0 c4 (ℓ "乊亲") (ℓ "亮乊") tt tt Eq.refl

wl0039 : Base 4 → ⟪ (ℓ "丳丫") ⟫ʷ ≈ ⟪ (ℓ "丫之") ⟫ʷ
wl0039 c4 = lw4 c4 (ℓ "丳丫") (ℓ "丫之") tt tt Eq.refl

wl0040 : Base 4 → ⟪ (ℓ "丘乊") ⟫ʷ ≈ ⟪ (ℓ "乊丒") ⟫ʷ
wl0040 c4 = lw4 c4 (ℓ "丘乊") (ℓ "乊丒") tt tt Eq.refl

wl0041 : Base 4 → ⟪ (ℓ "丘乢之乣之乎丘一") ⟫ʷ ≈ ⟪ (ℓ "丘乢之乣之乎丘丂") ⟫ʷ
wl0041 c4 = lw4 c4 (ℓ "丘乢之乣之乎丘一") (ℓ "丘乢之乣之乎丘丂") tt tt Eq.refl

wl0042 : Base 4 → ⟪ (ℓ "丷丫") ⟫ʷ ≈ ⟪ (ℓ "丫乏") ⟫ʷ
wl0042 c4 = lw4 c4 (ℓ "丷丫") (ℓ "丫乏") tt tt Eq.refl

wl0043 : Base 4 → ⟪ (ℓ "丷乊") ⟫ʷ ≈ ⟪ (ℓ "乊丷") ⟫ʷ
wl0043 c4 = lw4 c4 (ℓ "丷乊") (ℓ "乊丷") tt tt Eq.refl

wl0044 : Base 4 → ⟪ (ℓ "亰乊") ⟫ʷ ≈ ⟪ (ℓ "乊京") ⟫ʷ
wl0044 c4 = lw0 c4 (ℓ "亰乊") (ℓ "乊京") tt tt Eq.refl

wl0045 : Base 4 → ⟪ (ℓ "乊亮") ⟫ʷ ≈ ⟪ (ℓ "亲乊") ⟫ʷ
wl0045 c4 = lw0 c4 (ℓ "乊亮") (ℓ "亲乊") tt tt Eq.refl

wl0046 : Base 4 → ⟪ (ℓ "乎乊") ⟫ʷ ≈ ⟪ (ℓ "乊乢") ⟫ʷ
wl0046 c4 = lw4 c4 (ℓ "乎乊") (ℓ "乊乢") tt tt Eq.refl

wl0047 : Base 4 → ⟪ (ℓ "乢乊") ⟫ʷ ≈ ⟪ (ℓ "乊乎") ⟫ʷ
wl0047 c4 = lw4 c4 (ℓ "乢乊") (ℓ "乊乎") tt tt Eq.refl

wl0048 : Base 4 → ⟪ (ℓ "乖乥") ⟫ʷ ≈ ⟪ (ℓ "乥乖") ⟫ʷ
wl0048 c4 = lw0 c4 (ℓ "乖乥") (ℓ "乥乖") tt tt Eq.refl

wl0049 : Base 4 → ⟪ (ℓ "丸丫") ⟫ʷ ≈ ⟪ (ℓ "丫乐") ⟫ʷ
wl0049 c4 = lw4 c4 (ℓ "丸丫") (ℓ "丫乐") tt tt Eq.refl

wl0050 : Base 4 → ⟪ (ℓ "乙乊") ⟫ʷ ≈ ⟪ (ℓ "乊乭") ⟫ʷ
wl0050 c4 = lw0 c4 (ℓ "乙乊") (ℓ "乊乭") tt tt Eq.refl

wl0051 : Base 4 → ⟪ (ℓ "乭乊") ⟫ʷ ≈ ⟪ (ℓ "乊乙") ⟫ʷ
wl0051 c4 = lw0 c4 (ℓ "乭乊") (ℓ "乊乙") tt tt Eq.refl

wl0052 : Base 4 → ⟪ (ℓ "丫亥") ⟫ʷ ≈ ⟪ (ℓ "亙丫") ⟫ʷ
wl0052 c4 = lw4 c4 (ℓ "丫亥") (ℓ "亙丫") tt tt Eq.refl

wl0053 : Base 4 → ⟪ (ℓ "乫乊") ⟫ʷ ≈ ⟪ (ℓ "乊乗") ⟫ʷ
wl0053 c4 = lw0 c4 (ℓ "乫乊") (ℓ "乊乗") tt tt Eq.refl

wl0054 : Base 4 → ⟪ (ℓ "乊亱") ⟫ʷ ≈ ⟪ (ℓ "亭乊") ⟫ʷ
wl0054 c4 = lw0 c4 (ℓ "乊亱") (ℓ "亭乊") tt tt Eq.refl

wl0055 : Base 4 → ⟪ (ℓ "乥乼") ⟫ʷ ≈ ⟪ (ℓ "乬乥") ⟫ʷ
wl0055 c4 = lw0 c4 (ℓ "乥乼") (ℓ "乬乥") tt tt Eq.refl

wl0056 : Base 4 → ⟪ (ℓ "乥乬") ⟫ʷ ≈ ⟪ (ℓ "乼乥") ⟫ʷ
wl0056 c4 = lw0 c4 (ℓ "乥乬") (ℓ "乼乥") tt tt Eq.refl

wl0057 : Base 4 → ⟪ (ℓ "乳乊") ⟫ʷ ≈ ⟪ (ℓ "乊乶") ⟫ʷ
wl0057 c4 = lw4 c4 (ℓ "乳乊") (ℓ "乊乶") tt tt Eq.refl

wl0058 : Base 4 → ⟪ (ℓ "了乥") ⟫ʷ ≈ ⟪ (ℓ "乥争") ⟫ʷ
wl0058 c4 = lw0 c4 (ℓ "了乥") (ℓ "乥争") tt tt Eq.refl

wl0059 : Base 4 → ⟪ (ℓ "争乥") ⟫ʷ ≈ ⟪ (ℓ "乥了") ⟫ʷ
wl0059 c4 = lw0 c4 (ℓ "争乥") (ℓ "乥了") tt tt Eq.refl

wl0060 : Base 4 → ⟪ (ℓ "乶乊") ⟫ʷ ≈ ⟪ (ℓ "乊乳") ⟫ʷ
wl0060 c4 = lw4 c4 (ℓ "乶乊") (ℓ "乊乳") tt tt Eq.refl

wl0061 : Base 4 → ⟪ (ℓ "乤乘") ⟫ʷ ≈ ⟪ (ℓ "乘乤") ⟫ʷ
wl0061 c4 = lw0 c4 (ℓ "乤乘") (ℓ "乘乤") tt tt Eq.refl

wl0062 : Base 4 → ⟪ (ℓ "乗乥") ⟫ʷ ≈ ⟪ (ℓ "乥乗") ⟫ʷ
wl0062 c4 = lw0 c4 (ℓ "乗乥") (ℓ "乥乗") tt tt Eq.refl

wl0063 : Base 4 → ⟪ (ℓ "丫产") ⟫ʷ ≈ ⟪ (ℓ "些丫") ⟫ʷ
wl0063 c4 = lw4 c4 (ℓ "丫产") (ℓ "些丫") tt tt Eq.refl

wl0064 : Base 4 → ⟪ (ℓ "丞乥") ⟫ʷ ≈ ⟪ (ℓ "乥丘") ⟫ʷ
wl0064 c4 = lw4 c4 (ℓ "丞乥") (ℓ "乥丘") tt tt Eq.refl

wl0065 : Base 4 → ⟪ (ℓ "两乼") ⟫ʷ ≈ ⟪ (ℓ "乼丞") ⟫ʷ
wl0065 c4 = lw0 c4 (ℓ "两乼") (ℓ "乼丞") tt tt Eq.refl

wl0066 : Base 4 → ⟪ (ℓ "丞乼") ⟫ʷ ≈ ⟪ (ℓ "乼两") ⟫ʷ
wl0066 c4 = lw0 c4 (ℓ "丞乼") (ℓ "乼两") tt tt Eq.refl

wl0067 : Base 4 → ⟪ (ℓ "丘乥") ⟫ʷ ≈ ⟪ (ℓ "乥丞") ⟫ʷ
wl0067 c4 = lw4 c4 (ℓ "丘乥") (ℓ "乥丞") tt tt Eq.refl

wl0068 : Base 4 → ⟪ (ℓ "丞乢之乣之乎丞一") ⟫ʷ ≈ ⟪ (ℓ "丞乢之乣之乎丞丂") ⟫ʷ
wl0068 c4 = lw4 c4 (ℓ "丞乢之乣之乎丞一") (ℓ "丞乢之乣之乎丞丂") tt tt Eq.refl

wl0069 : Base 4 → ⟪ (ℓ "亃乊") ⟫ʷ ≈ ⟪ (ℓ "乊了") ⟫ʷ
wl0069 c4 = lw0 c4 (ℓ "亃乊") (ℓ "乊了") tt tt Eq.refl

wl0070 : Base 4 → ⟪ (ℓ "亃乥") ⟫ʷ ≈ ⟪ (ℓ "乥亃") ⟫ʷ
wl0070 c4 = lw0 c4 (ℓ "亃乥") (ℓ "乥亃") tt tt Eq.refl

wl0071 : Base 4 → ⟪ (ℓ "乙乥") ⟫ʷ ≈ ⟪ (ℓ "乥乙") ⟫ʷ
wl0071 c4 = lw0 c4 (ℓ "乙乥") (ℓ "乥乙") tt tt Eq.refl

wl0072 : Base 4 → ⟪ (ℓ "乊乬") ⟫ʷ ≈ ⟪ (ℓ "乘乊") ⟫ʷ
wl0072 c4 = lw0 c4 (ℓ "乊乬") (ℓ "乘乊") tt tt Eq.refl

wl0073 : Base 4 → ⟪ (ℓ "丒乊") ⟫ʷ ≈ ⟪ (ℓ "乊丘") ⟫ʷ
wl0073 c4 = lw4 c4 (ℓ "丒乊") (ℓ "乊丘") tt tt Eq.refl

wl0074 : Base 4 → ⟪ (ℓ "乘乥") ⟫ʷ ≈ ⟪ (ℓ "乥乘") ⟫ʷ
wl0074 c4 = lw0 c4 (ℓ "乘乥") (ℓ "乥乘") tt tt Eq.refl

wl0075 : Base 4 → ⟪ (ℓ "乊乥") ⟫ʷ ≈ ⟪ (ℓ "乑乊") ⟫ʷ
wl0075 c4 = lw4 c4 (ℓ "乊乥") (ℓ "乑乊") tt tt Eq.refl

wl0076 : Base 4 → ⟪ (ℓ "丱丫") ⟫ʷ ≈ ⟪ (ℓ "丫义") ⟫ʷ
wl0076 c4 = lw4 c4 (ℓ "丱丫") (ℓ "丫义") tt tt Eq.refl

wl0077 : Base 4 → ⟪ (ℓ "乜丫") ⟫ʷ ≈ ⟪ (ℓ "丫也") ⟫ʷ
wl0077 c4 = lw4 c4 (ℓ "乜丫") (ℓ "丫也") tt tt Eq.refl

wl0078 : Base 4 → ⟪ (ℓ "买丫") ⟫ʷ ≈ ⟪ (ℓ "丫乳") ⟫ʷ
wl0078 c4 = lw4 c4 (ℓ "买丫") (ℓ "丫乳") tt tt Eq.refl

wl0079 : Base 4 → ⟪ (ℓ "丸乊") ⟫ʷ ≈ ⟪ (ℓ "乊丸") ⟫ʷ
wl0079 c4 = lw4 c4 (ℓ "丸乊") (ℓ "乊丸") tt tt Eq.refl

wl0080 : Base 4 → ⟪ (ℓ "买乊") ⟫ʷ ≈ ⟪ (ℓ "乊买") ⟫ʷ
wl0080 c4 = lw4 c4 (ℓ "买乊") (ℓ "乊买") tt tt Eq.refl

wl0081 : Base 4 → ⟪ (ℓ "乱丫") ⟫ʷ ≈ ⟪ (ℓ "丫乴") ⟫ʷ
wl0081 c4 = lw4 c4 (ℓ "乱丫") (ℓ "丫乴") tt tt Eq.refl

wl0082 : Base 4 → ⟪ (ℓ "乲丫") ⟫ʷ ≈ ⟪ (ℓ "丫乵") ⟫ʷ
wl0082 c4 = lw4 c4 (ℓ "乲丫") (ℓ "丫乵") tt tt Eq.refl

wl0083 : Base 4 → ⟪ (ℓ "乊亭") ⟫ʷ ≈ ⟪ (ℓ "亱乊") ⟫ʷ
wl0083 c4 = lw0 c4 (ℓ "乊亭") (ℓ "亱乊") tt tt Eq.refl

wl0084 : Base 4 → ⟪ (ℓ "乊亯") ⟫ʷ ≈ ⟪ (ℓ "亳乊") ⟫ʷ
wl0084 c4 = lw0 c4 (ℓ "乊亯") (ℓ "亳乊") tt tt Eq.refl

wl0085 : Base 4 → ⟪ (ℓ "乊亳") ⟫ʷ ≈ ⟪ (ℓ "亯乊") ⟫ʷ
wl0085 c4 = lw0 c4 (ℓ "乊亳") (ℓ "亯乊") tt tt Eq.refl

wl0086 : Base 4 → ⟪ (ℓ "义丹") ⟫ʷ ≈ ⟪ (ℓ "丹义") ⟫ʷ
wl0086 c4 = lw4 c4 (ℓ "义丹") (ℓ "丹义") tt tt Eq.refl

wl0087 : Base 4 → ⟪ (ℓ "亄乊") ⟫ʷ ≈ ⟪ (ℓ "乊亇") ⟫ʷ
wl0087 c4 = lw0 c4 (ℓ "亄乊") (ℓ "乊亇") tt tt Eq.refl

wl0088 : Base 4 → ⟪ (ℓ "乱乊") ⟫ʷ ≈ ⟪ (ℓ "乊乱") ⟫ʷ
wl0088 c4 = lw4 c4 (ℓ "乱乊") (ℓ "乊乱") tt tt Eq.refl

wl0089 : Base 4 → ⟪ (ℓ "了乊") ⟫ʷ ≈ ⟪ (ℓ "乊亃") ⟫ʷ
wl0089 c4 = lw0 c4 (ℓ "了乊") (ℓ "乊亃") tt tt Eq.refl

wl0090 : Base 4 → ⟪ (ℓ "亇乥") ⟫ʷ ≈ ⟪ (ℓ "乥亊") ⟫ʷ
wl0090 c4 = lw0 c4 (ℓ "亇乥") (ℓ "乥亊") tt tt Eq.refl

wl0091 : Base 4 → ⟪ (ℓ "亊乥") ⟫ʷ ≈ ⟪ (ℓ "乥亇") ⟫ʷ
wl0091 c4 = lw0 c4 (ℓ "亊乥") (ℓ "乥亇") tt tt Eq.refl

wl0092 : Base 4 → ⟪ (ℓ "亇乊") ⟫ʷ ≈ ⟪ (ℓ "乊亄") ⟫ʷ
wl0092 c4 = lw0 c4 (ℓ "亇乊") (ℓ "乊亄") tt tt Eq.refl

wl0093 : Base 4 → ⟪ (ℓ "乊乘") ⟫ʷ ≈ ⟪ (ℓ "乬乊") ⟫ʷ
wl0093 c4 = lw0 c4 (ℓ "乊乘") (ℓ "乬乊") tt tt Eq.refl

wl0094 : Base 4 → ⟪ (ℓ "乷乊") ⟫ʷ ≈ ⟪ (ℓ "乊乴") ⟫ʷ
wl0094 c4 = lw4 c4 (ℓ "乷乊") (ℓ "乊乴") tt tt Eq.refl

wl0095 : Base 4 → ⟪ (ℓ "乴乊") ⟫ʷ ≈ ⟪ (ℓ "乊乷") ⟫ʷ
wl0095 c4 = lw4 c4 (ℓ "乴乊") (ℓ "乊乷") tt tt Eq.refl

wl0096 : Base 4 → ⟪ (ℓ "乊乑") ⟫ʷ ≈ ⟪ (ℓ "乥乊") ⟫ʷ
wl0096 c4 = lw4 c4 (ℓ "乊乑") (ℓ "乥乊") tt tt Eq.refl

wl0097 : Base 4 → ⟪ (ℓ "丹乊") ⟫ʷ ≈ ⟪ (ℓ "乊丹") ⟫ʷ
wl0097 c4 = lw4 c4 (ℓ "丹乊") (ℓ "乊丹") tt tt Eq.refl

wl0098 : Base 4 → ⟪ (ℓ "丫乑") ⟫ʷ ≈ ⟪ (ℓ "丹丫") ⟫ʷ
wl0098 c4 = lw4 c4 (ℓ "丫乑") (ℓ "丹丫") tt tt Eq.refl

wl0099 : Base 4 → ⟪ (ℓ "亄乥") ⟫ʷ ≈ ⟪ (ℓ "乥亄") ⟫ʷ
wl0099 c4 = lw0 c4 (ℓ "亄乥") (ℓ "乥亄") tt tt Eq.refl

wl0100 : Base 4 → ⟪ (ℓ "丫乊") ⟫ʷ ≈ ⟪ (ℓ "串丫") ⟫ʷ
wl0100 c4 = lw4 c4 (ℓ "丫乊") (ℓ "串丫") tt tt Eq.refl

wl0101 : Base 4 → ⟪ (ℓ "二乊") ⟫ʷ ≈ ⟪ (ℓ "乊二") ⟫ʷ
wl0101 c4 = lw4 c4 (ℓ "二乊") (ℓ "乊二") tt tt Eq.refl

wl0102 : Base 4 → ⟪ (ℓ "乊亍") ⟫ʷ ≈ ⟪ (ℓ "亍乊") ⟫ʷ
wl0102 c4 = lw4 c4 (ℓ "乊亍") (ℓ "亍乊") tt tt Eq.refl

wl0103 : Base 4 → ⟪ (ℓ "二丫") ⟫ʷ ≈ ⟪ (ℓ "丫二") ⟫ʷ
wl0103 c4 = lw4 c4 (ℓ "二丫") (ℓ "丫二") tt tt Eq.refl

wl0104 : Base 4 → ⟪ (ℓ "丫于") ⟫ʷ ≈ ⟪ (ℓ "亍丫") ⟫ʷ
wl0104 c4 = lw4 c4 (ℓ "丫于") (ℓ "亍丫") tt tt Eq.refl

wl0105 : Base 4 → ⟪ (ℓ "乏丫") ⟫ʷ ≈ ⟪ (ℓ "丫丷") ⟫ʷ
wl0105 c4 = lw4 c4 (ℓ "乏丫") (ℓ "丫丷") tt tt Eq.refl

wl0106 : Base 4 → ⟪ (ℓ "乎丫") ⟫ʷ ≈ ⟪ (ℓ "丫丶") ⟫ʷ
wl0106 c4 = lw4 c4 (ℓ "乎丫") (ℓ "丫丶") tt tt Eq.refl

wl0107 : Base 4 → ⟪ (ℓ "丬丫") ⟫ʷ ≈ ⟪ (ℓ "丫乄") ⟫ʷ
wl0107 c4 = lw4 c4 (ℓ "丬丫") (ℓ "丫乄") tt tt Eq.refl

wl0108 : Base 4 → ⟪ (ℓ "丯乄丰乄乇") ⟫ʷ ≈ ⟪ (ℓ "乇丬么丬丯") ⟫ʷ
wl0108 c4 = lw4 c4 (ℓ "丯乄丰乄乇") (ℓ "乇丬么丬丯") tt tt Eq.refl

wl0109 : Base 4 → ⟪ (ℓ "丒丫") ⟫ʷ ≈ ⟪ (ℓ "丫丌") ⟫ʷ
wl0109 c4 = lw4 c4 (ℓ "丒丫") (ℓ "丫丌") tt tt Eq.refl

wl0110 : Base 4 → ⟪ (ℓ "丌丯乄丰乄乇丌一") ⟫ʷ ≈ ⟪ (ℓ "丌乇丬么丬丯丌一") ⟫ʷ
wl0110 c4 = lw4 c4 (ℓ "丌丯乄丰乄乇丌一") (ℓ "丌乇丬么丬丯丌一") tt tt Eq.refl

wl0111 : Base 4 → ⟪ (ℓ "乥亱") ⟫ʷ ≈ ⟪ (ℓ "亲乥") ⟫ʷ
wl0111 c4 = lw0 c4 (ℓ "乥亱") (ℓ "亲乥") tt tt Eq.refl

wl0112 : Base 4 → ⟪ (ℓ "么乊") ⟫ʷ ≈ ⟪ (ℓ "乊么") ⟫ʷ
wl0112 c4 = lw4 c4 (ℓ "么乊") (ℓ "乊么") tt tt Eq.refl

wl0113 : Base 4 → ⟪ (ℓ "乇乊") ⟫ʷ ≈ ⟪ (ℓ "乊乇") ⟫ʷ
wl0113 c4 = lw4 c4 (ℓ "乇乊") (ℓ "乊乇") tt tt Eq.refl

wl0114 : Base 4 → ⟪ (ℓ "义乊") ⟫ʷ ≈ ⟪ (ℓ "乊义") ⟫ʷ
wl0114 c4 = lw4 c4 (ℓ "义乊") (ℓ "乊义") tt tt Eq.refl

wl0115 : Base 4 → ⟪ (ℓ "乄丫") ⟫ʷ ≈ ⟪ (ℓ "丫丬") ⟫ʷ
wl0115 c4 = lw4 c4 (ℓ "乄丫") (ℓ "丫丬") tt tt Eq.refl

wl0116 : Base 4 → ⟪ (ℓ "丒丯乄丰乄乇丒一") ⟫ʷ ≈ ⟪ (ℓ "丒乇丬么丬丯丒一") ⟫ʷ
wl0116 c4 = lw4 c4 (ℓ "丒丯乄丰乄乇丒一") (ℓ "丒乇丬么丬丯丒一") tt tt Eq.refl

wl0117 : Base 4 → ⟪ (ℓ "之丫") ⟫ʷ ≈ ⟪ (ℓ "丫丳") ⟫ʷ
wl0117 c4 = lw4 c4 (ℓ "之丫") (ℓ "丫丳") tt tt Eq.refl

wl0118 : Base 4 → ⟪ (ℓ "丫丂") ⟫ʷ ≈ ⟪ (ℓ "丂丫") ⟫ʷ
wl0118 c4 = lw4 c4 (ℓ "丫丂") (ℓ "丂丫") tt tt Eq.refl

wl0119 : Base 4 → ⟪ (ℓ "乊丂") ⟫ʷ ≈ ⟪ (ℓ "丂乊") ⟫ʷ
wl0119 c4 = lw4 c4 (ℓ "乊丂") (ℓ "丂乊") tt tt Eq.refl

wl0120 : Base 4 → ⟪ (ℓ "丘乇丬么丬丯丘一") ⟫ʷ ≈ ⟪ (ℓ "丘乇丬么丬丯丘丂") ⟫ʷ
wl0120 c4 = lw4 c4 (ℓ "丘乇丬么丬丯丘一") (ℓ "丘乇丬么丬丯丘丂") tt tt Eq.refl

wl0121 : Base 4 → ⟪ (ℓ "丫亓") ⟫ʷ ≈ ⟪ (ℓ "亓丫") ⟫ʷ
wl0121 c4 = lw4 c4 (ℓ "丫亓") (ℓ "亓丫") tt tt Eq.refl

wl0122 : Base 4 → ⟪ (ℓ "亨乊") ⟫ʷ ≈ ⟪ (ℓ "乊亨") ⟫ʷ
wl0122 c4 = lw0 c4 (ℓ "亨乊") (ℓ "乊亨") tt tt Eq.refl

wl0123 : Base 4 → ⟪ (ℓ "乊亩") ⟫ʷ ≈ ⟪ (ℓ "亪乊") ⟫ʷ
wl0123 c4 = lw0 c4 (ℓ "乊亩") (ℓ "亪乊") tt tt Eq.refl

wl0124 : Base 4 → ⟪ (ℓ "丘丯乄丰乄乇丘一") ⟫ʷ ≈ ⟪ (ℓ "丘乇丬么丬丯丘一") ⟫ʷ
wl0124 c4 = lw4 c4 (ℓ "丘丯乄丰乄乇丘一") (ℓ "丘乇丬么丬丯丘一") tt tt Eq.refl

wl0125 : Base 4 → ⟪ (ℓ "丌乇丬么丬丯丌一") ⟫ʷ ≈ ⟪ (ℓ "丌乇丬么丬丯丌丂") ⟫ʷ
wl0125 c4 = lw4 c4 (ℓ "丌乇丬么丬丯丌一") (ℓ "丌乇丬么丬丯丌丂") tt tt Eq.refl

wl0126 : Base 4 → ⟪ (ℓ "乥亦") ⟫ʷ ≈ ⟪ (ℓ "产乥") ⟫ʷ
wl0126 c4 = lw4 c4 (ℓ "乥亦") (ℓ "产乥") tt tt Eq.refl

wl0127 : Base 4 → ⟪ (ℓ "乊亥") ⟫ʷ ≈ ⟪ (ℓ "亦乊") ⟫ʷ
wl0127 c4 = lw4 c4 (ℓ "乊亥") (ℓ "亦乊") tt tt Eq.refl

wl0128 : Base 4 → ⟪ (ℓ "乺乼") ⟫ʷ ≈ ⟪ (ℓ "乼乺") ⟫ʷ
wl0128 c4 = lw0 c4 (ℓ "乺乼") (ℓ "乼乺") tt tt Eq.refl

wl0129 : Base 4 → ⟪ (ℓ "乹乼") ⟫ʷ ≈ ⟪ (ℓ "乼乹") ⟫ʷ
wl0129 c4 = lw0 c4 (ℓ "乹乼") (ℓ "乼乹") tt tt Eq.refl

wl0130 : Base 4 → ⟪ (ℓ "乇丬么丬丯") ⟫ʷ ≈ ⟪ (ℓ "乇丳么丳丨") ⟫ʷ
wl0130 c4 = lw4 c4 (ℓ "乇丬么丬丯") (ℓ "乇丳么丳丨") tt tt Eq.refl

wl0131 : Base 4 → ⟪ (ℓ "丌乇丬么丬丯丌一") ⟫ʷ ≈ ⟪ (ℓ "丌乇丳么丳丨丌一") ⟫ʷ
wl0131 c4 = lw4 c4 (ℓ "丌乇丬么丬丯丌一") (ℓ "丌乇丳么丳丨丌一") tt tt Eq.refl

wl0132 : Base 4 → ⟪ (ℓ "亘乥") ⟫ʷ ≈ ⟪ (ℓ "乥亘") ⟫ʷ
wl0132 c4 = lw4 c4 (ℓ "亘乥") (ℓ "乥亘") tt tt Eq.refl

wl0133 : Base 4 → ⟪ (ℓ "乥亚") ⟫ʷ ≈ ⟪ (ℓ "些乥") ⟫ʷ
wl0133 c4 = lw4 c4 (ℓ "乥亚") (ℓ "些乥") tt tt Eq.refl

wl0134 : Base 4 → ⟪ (ℓ "丒乇丬么丬丯丒一") ⟫ʷ ≈ ⟪ (ℓ "丒乇丬么丬丯丒丂") ⟫ʷ
wl0134 c4 = lw4 c4 (ℓ "丒乇丬么丬丯丒一") (ℓ "丒乇丬么丬丯丒丂") tt tt Eq.refl

wl0135 : Base 4 → ⟪ (ℓ "交丫") ⟫ʷ ≈ ⟪ (ℓ "丫亘") ⟫ʷ
wl0135 c4 = lw4 c4 (ℓ "交丫") (ℓ "丫亘") tt tt Eq.refl

wl0136 : Base 4 → ⟪ (ℓ "丫亚") ⟫ʷ ≈ ⟪ (ℓ "亦丫") ⟫ʷ
wl0136 c4 = lw4 c4 (ℓ "丫亚") (ℓ "亦丫") tt tt Eq.refl

wl0137 : Base 4 → ⟪ (ℓ "交乊") ⟫ʷ ≈ ⟪ (ℓ "乊交") ⟫ʷ
wl0137 c4 = lw4 c4 (ℓ "交乊") (ℓ "乊交") tt tt Eq.refl

wl0138 : Base 4 → ⟪ (ℓ "乊亦") ⟫ʷ ≈ ⟪ (ℓ "亥乊") ⟫ʷ
wl0138 c4 = lw4 c4 (ℓ "乊亦") (ℓ "亥乊") tt tt Eq.refl

wl0139 : Base 4 → ⟪ (ℓ "交乥") ⟫ʷ ≈ ⟪ (ℓ "乥交") ⟫ʷ
wl0139 c4 = lw4 c4 (ℓ "交乥") (ℓ "乥交") tt tt Eq.refl

wl0140 : Base 4 → ⟪ (ℓ "乥亥") ⟫ʷ ≈ ⟪ (ℓ "亥乥") ⟫ʷ
wl0140 c4 = lw4 c4 (ℓ "乥亥") (ℓ "亥乥") tt tt Eq.refl

wl0141 : Base 4 → ⟪ (ℓ "京乼") ⟫ʷ ≈ ⟪ (ℓ "乼京") ⟫ʷ
wl0141 c4 = lw0 c4 (ℓ "京乼") (ℓ "乼京") tt tt Eq.refl

wl0142 : Base 4 → ⟪ (ℓ "乼亮") ⟫ʷ ≈ ⟪ (ℓ "亯乼") ⟫ʷ
wl0142 c4 = lw0 c4 (ℓ "乼亮") (ℓ "亯乼") tt tt Eq.refl

wl0143 : Base 4 → ⟪ (ℓ "乥亙") ⟫ʷ ≈ ⟪ (ℓ "亙乥") ⟫ʷ
wl0143 c4 = lw4 c4 (ℓ "乥亙") (ℓ "亙乥") tt tt Eq.refl

wl0144 : Base 4 → ⟪ (ℓ "乊享") ⟫ʷ ≈ ⟪ (ℓ "享乊") ⟫ʷ
wl0144 c4 = lw0 c4 (ℓ "乊享") (ℓ "享乊") tt tt Eq.refl

wl0145 : Base 4 → ⟪ (ℓ "义丫") ⟫ʷ ≈ ⟪ (ℓ "丫丱") ⟫ʷ
wl0145 c4 = lw4 c4 (ℓ "义丫") (ℓ "丫丱") tt tt Eq.refl

wl0146 : Base 4 → ⟪ (ℓ "乇丫") ⟫ʷ ≈ ⟪ (ℓ "丫丯") ⟫ʷ
wl0146 c4 = lw4 c4 (ℓ "乇丫") (ℓ "丫丯") tt tt Eq.refl

wl0147 : Base 4 → ⟪ (ℓ "么丫") ⟫ʷ ≈ ⟪ (ℓ "丫丰") ⟫ʷ
wl0147 c4 = lw4 c4 (ℓ "么丫") (ℓ "丫丰") tt tt Eq.refl

wl0148 : Base 4 → ⟪ (ℓ "丫云") ⟫ʷ ≈ ⟪ (ℓ "互丫") ⟫ʷ
wl0148 c4 = lw4 c4 (ℓ "丫云") (ℓ "互丫") tt tt Eq.refl

wl0149 : Base 4 → ⟪ (ℓ "丘乇丬么丬丯丘一") ⟫ʷ ≈ ⟪ (ℓ "丘乇丳么丳丨丘一") ⟫ʷ
wl0149 c4 = lw4 c4 (ℓ "丘乇丬么丬丯丘一") (ℓ "丘乇丳么丳丨丘一") tt tt Eq.refl

wl0150 : Base 4 → ⟪ (ℓ "乊产") ⟫ʷ ≈ ⟪ (ℓ "产乊") ⟫ʷ
wl0150 c4 = lw4 c4 (ℓ "乊产") (ℓ "产乊") tt tt Eq.refl

wl0151 : Base 4 → ⟪ (ℓ "乐丫") ⟫ʷ ≈ ⟪ (ℓ "丫丸") ⟫ʷ
wl0151 c4 = lw4 c4 (ℓ "乐丫") (ℓ "丫丸") tt tt Eq.refl

wl0152 : Base 4 → ⟪ (ℓ "主丫") ⟫ʷ ≈ ⟪ (ℓ "丫乓") ⟫ʷ
wl0152 c4 = lw4 c4 (ℓ "主丫") (ℓ "丫乓") tt tt Eq.refl

wl0153 : Base 4 → ⟪ (ℓ "临丫") ⟫ʷ ≈ ⟪ (ℓ "丫乌") ⟫ʷ
wl0153 c4 = lw4 c4 (ℓ "临丫") (ℓ "丫乌") tt tt Eq.refl

wl0154 : Base 4 → ⟪ (ℓ "主乊") ⟫ʷ ≈ ⟪ (ℓ "乊主") ⟫ʷ
wl0154 c4 = lw4 c4 (ℓ "主乊") (ℓ "乊主") tt tt Eq.refl

wl0155 : Base 4 → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "丯之丰之丨") ⟫ʷ
wl0155 c4 = lw4 c4 (ℓ "二") (ℓ "丯之丰之丨") tt tt Eq.refl

wl0156 : Base 4 → ⟪ (ℓ "丌二不") ⟫ʷ ≈ ⟪ (ℓ "亍") ⟫ʷ
wl0156 c4 = lw4 c4 (ℓ "丌二不") (ℓ "亍") tt tt Eq.refl

wl0157 : Base 4 → ⟪ (ℓ "不丌") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0157 c4 = lw4 c4 (ℓ "不丌") [] tt tt Eq.refl

wl0158 : Base 4 → ⟪ (ℓ "么上亍下") ⟫ʷ ≈ ⟪ (ℓ "亍二") ⟫ʷ
wl0158 c4 = lw4 c4 (ℓ "么上亍下") (ℓ "亍二") tt tt Eq.refl

wl0159 : Base 4 → ⟪ (ℓ "下上") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0159 c4 = lw4 c4 (ℓ "下上") [] tt tt Eq.refl

wl0160 : Base 4 → ⟪ (ℓ "二亍") ⟫ʷ ≈ ⟪ (ℓ "亍二义") ⟫ʷ
wl0160 c4 = lw4 c4 (ℓ "二亍") (ℓ "亍二义") tt tt Eq.refl

wl0161 : Base 4 → ⟪ (ℓ "二义亍二") ⟫ʷ ≈ ⟪ (ℓ "亍") ⟫ʷ
wl0161 c4 = lw4 c4 (ℓ "二义亍二") (ℓ "亍") tt tt Eq.refl

wl0162 : Base 4 → ⟪ (ℓ "亍亍") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0162 c4 = lw4 c4 (ℓ "亍亍") [] tt tt Eq.refl

wl0163 : Base 4 → ⟪ (ℓ "二亍义") ⟫ʷ ≈ ⟪ (ℓ "亍二") ⟫ʷ
wl0163 c4 = lw4 c4 (ℓ "二亍义") (ℓ "亍二") tt tt Eq.refl

wl0164 : Base 4 → ⟪ (ℓ "二亍") ⟫ʷ ≈ ⟪ (ℓ "亍义二") ⟫ʷ
wl0164 c4 = lw4 c4 (ℓ "二亍") (ℓ "亍义二") tt tt Eq.refl

wl0165 : Base 4 → ⟪ (ℓ "二业个") ⟫ʷ ≈ ⟪ (ℓ "业二") ⟫ʷ
wl0165 c4 = lw4 c4 (ℓ "二业个") (ℓ "业二") tt tt Eq.refl

wl0166 : Base 4 → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "乹乒乺乒乕") ⟫ʷ
wl0166 c4 = lw0 c4 (ℓ "京") (ℓ "乹乒乺乒乕") tt tt Eq.refl

wl0167 : Base 4 → ⟪ (ℓ "二乒") ⟫ʷ ≈ ⟪ (ℓ "乒二") ⟫ʷ
wl0167 c4 = lw4 c4 (ℓ "二乒") (ℓ "乒二") tt tt Eq.refl

wl0168 : Base 4 → ⟪ (ℓ "二个") ⟫ʷ ≈ ⟪ (ℓ "个二") ⟫ʷ
wl0168 c4 = lw4 c4 (ℓ "二个") (ℓ "个二") tt tt Eq.refl

wl0169 : Base 4 → ⟪ (ℓ "业个个") ⟫ʷ ≈ ⟪ (ℓ "业") ⟫ʷ
wl0169 c4 = lw4 c4 (ℓ "业个个") (ℓ "业") tt tt Eq.refl

wl0170 : Base 4 → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "业京业") ⟫ʷ
wl0170 c4 = lw0 c4 (ℓ "京") (ℓ "业京业") tt tt Eq.refl

wl0171 : Base 4 → ⟪ (ℓ "交丯") ⟫ʷ ≈ ⟪ (ℓ "丯交") ⟫ʷ
wl0171 c4 = lw4 c4 (ℓ "交丯") (ℓ "丯交") tt tt Eq.refl

wl0172 : Base 4 → ⟪ (ℓ "交乪") ⟫ʷ ≈ ⟪ (ℓ "乪交") ⟫ʷ
wl0172 c4 = lw0 c4 (ℓ "交乪") (ℓ "乪交") tt tt Eq.refl

wl0173 : Base 4 → ⟪ (ℓ "交乩") ⟫ʷ ≈ ⟪ (ℓ "乩交") ⟫ʷ
wl0173 c4 = lw0 c4 (ℓ "交乩") (ℓ "乩交") tt tt Eq.refl

wl0174 : Base 4 → ⟪ (ℓ "丘交丙") ⟫ʷ ≈ ⟪ (ℓ "亦") ⟫ʷ
wl0174 c4 = lw4 c4 (ℓ "丘交丙") (ℓ "亦") tt tt Eq.refl

wl0175 : Base 4 → ⟪ (ℓ "丙丘") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0175 c4 = lw4 c4 (ℓ "丙丘") [] tt tt Eq.refl

wl0176 : Base 4 → ⟪ (ℓ "乏世亦丗") ⟫ʷ ≈ ⟪ (ℓ "亦交") ⟫ʷ
wl0176 c4 = lw4 c4 (ℓ "乏世亦丗") (ℓ "亦交") tt tt Eq.refl

wl0177 : Base 4 → ⟪ (ℓ "乏丗") ⟫ʷ ≈ ⟪ (ℓ "丗乏") ⟫ʷ
wl0177 c4 = lw4 c4 (ℓ "乏丗") (ℓ "丗乏") tt tt Eq.refl

wl0178 : Base 4 → ⟪ (ℓ "乏世") ⟫ʷ ≈ ⟪ (ℓ "世乏") ⟫ʷ
wl0178 c4 = lw4 c4 (ℓ "乏世") (ℓ "世乏") tt tt Eq.refl

wl0179 : Base 4 → ⟪ (ℓ "丗世") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0179 c4 = lw4 c4 (ℓ "丗世") [] tt tt Eq.refl

wl0180 : Base 4 → ⟪ (ℓ "亦亦") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0180 c4 = lw4 c4 (ℓ "亦亦") [] tt tt Eq.refl

wl0181 : Base 4 → ⟪ (ℓ "交交") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0181 c4 = lw4 c4 (ℓ "交交") [] tt tt Eq.refl

wl0182 : Base 4 → ⟪ (ℓ "二亍丸亍二丸") ⟫ʷ ≈ ⟪ (ℓ "交") ⟫ʷ
wl0182 c4 = lw4 c4 (ℓ "二亍丸亍二丸") (ℓ "交") tt tt Eq.refl

wl0183 : Base 4 → ⟪ (ℓ "丱亦") ⟫ʷ ≈ ⟪ (ℓ "亦丱亐") ⟫ʷ
wl0183 c4 = lw4 c4 (ℓ "丱亦") (ℓ "亦丱亐") tt tt Eq.refl

wl0184 : Base 4 → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "乎丬乏丬丶") ⟫ʷ
wl0184 c4 = lw4 c4 (ℓ "亐") (ℓ "乎丬乏丬丶") tt tt Eq.refl

wl0185 : Base 4 → ⟪ (ℓ "並丱丱") ⟫ʷ ≈ ⟪ (ℓ "並") ⟫ʷ
wl0185 c4 = lw3 c4 (ℓ "並丱丱") (ℓ "並") tt tt Eq.refl

wl0186 : Base 4 → ⟪ (ℓ "亐亦") ⟫ʷ ≈ ⟪ (ℓ "亦亐") ⟫ʷ
wl0186 c4 = lw4 c4 (ℓ "亐亦") (ℓ "亦亐") tt tt Eq.refl

wl0187 : Base 4 → ⟪ (ℓ "亮並") ⟫ʷ ≈ ⟪ (ℓ "並乒亮") ⟫ʷ
wl0187 c4 = lw0 c4 (ℓ "亮並") (ℓ "並乒亮") tt tt Eq.refl

wl0188 : Base 4 → ⟪ (ℓ "丶乒") ⟫ʷ ≈ ⟪ (ℓ "乒丨亐丶") ⟫ʷ
wl0188 c4 = lw4 c4 (ℓ "丶乒") (ℓ "乒丨亐丶") tt tt Eq.refl

wl0189 : Base 4 → ⟪ (ℓ "乒亮") ⟫ʷ ≈ ⟪ (ℓ "亮乒") ⟫ʷ
wl0189 c4 = lw0 c4 (ℓ "乒亮") (ℓ "亮乒") tt tt Eq.refl

wl0190 : Base 4 → ⟪ (ℓ "丞乹乒乺乒乕丟") ⟫ʷ ≈ ⟪ (ℓ "亮") ⟫ʷ
wl0190 c4 = lw0 c4 (ℓ "丞乹乒乺乒乕丟") (ℓ "亮") tt tt Eq.refl

wl0191 : Base 4 → ⟪ (ℓ "丷亦") ⟫ʷ ≈ ⟪ (ℓ "亦丷") ⟫ʷ
wl0191 c4 = lw4 c4 (ℓ "丷亦") (ℓ "亦丷") tt tt Eq.refl

wl0192 : Base 4 → ⟪ (ℓ "亦亪亮") ⟫ʷ ≈ ⟪ (ℓ "亮亦") ⟫ʷ
wl0192 c4 = lw0 c4 (ℓ "亦亪亮") (ℓ "亮亦") tt tt Eq.refl

wl0193 : Base 4 → ⟪ (ℓ "丨亦") ⟫ʷ ≈ ⟪ (ℓ "亦丨") ⟫ʷ
wl0193 c4 = lw4 c4 (ℓ "丨亦") (ℓ "亦丨") tt tt Eq.refl

wl0194 : Base 4 → ⟪ (ℓ "乖亦") ⟫ʷ ≈ ⟪ (ℓ "亦乖") ⟫ʷ
wl0194 c4 = lw0 c4 (ℓ "乖亦") (ℓ "亦乖") tt tt Eq.refl

wl0195 : Base 4 → ⟪ (ℓ "乕亦") ⟫ʷ ≈ ⟪ (ℓ "亦乕") ⟫ʷ
wl0195 c4 = lw0 c4 (ℓ "乕亦") (ℓ "亦乕") tt tt Eq.refl

wl0196 : Base 4 → ⟪ (ℓ "丶亦") ⟫ʷ ≈ ⟪ (ℓ "亦丶") ⟫ʷ
wl0196 c4 = lw4 c4 (ℓ "丶亦") (ℓ "亦丶") tt tt Eq.refl

wl0197 : Base 4 → ⟪ (ℓ "亦亪") ⟫ʷ ≈ ⟪ (ℓ "亪亦") ⟫ʷ
wl0197 c4 = lw0 c4 (ℓ "亦亪") (ℓ "亪亦") tt tt Eq.refl

wl0198 : Base 4 → ⟪ (ℓ "亪亪亮") ⟫ʷ ≈ ⟪ (ℓ "亮") ⟫ʷ
wl0198 c4 = lw0 c4 (ℓ "亪亪亮") (ℓ "亮") tt tt Eq.refl

wl0199 : Base 4 → ⟪ (ℓ "亘丨") ⟫ʷ ≈ ⟪ (ℓ "丨亘") ⟫ʷ
wl0199 c4 = lw4 c4 (ℓ "亘丨") (ℓ "丨亘") tt tt Eq.refl

wl0200 : Base 4 → ⟪ (ℓ "丌亘不") ⟫ʷ ≈ ⟪ (ℓ "亙") ⟫ʷ
wl0200 c4 = lw4 c4 (ℓ "丌亘不") (ℓ "亙") tt tt Eq.refl

wl0201 : Base 4 → ⟪ (ℓ "乣上亙下") ⟫ʷ ≈ ⟪ (ℓ "亙亘") ⟫ʷ
wl0201 c4 = lw4 c4 (ℓ "乣上亙下") (ℓ "亙亘") tt tt Eq.refl

wl0202 : Base 4 → ⟪ (ℓ "乖乣") ⟫ʷ ≈ ⟪ (ℓ "乣乖") ⟫ʷ
wl0202 c4 = lw0 c4 (ℓ "乖乣") (ℓ "乣乖") tt tt Eq.refl

wl0203 : Base 4 → ⟪ (ℓ "亙亙") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0203 c4 = lw4 c4 (ℓ "亙亙") [] tt tt Eq.refl

wl0204 : Base 4 → ⟪ (ℓ "亘亘") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0204 c4 = lw4 c4 (ℓ "亘亘") [] tt tt Eq.refl

wl0205 : Base 4 → ⟪ (ℓ "二于乐于二乐") ⟫ʷ ≈ ⟪ (ℓ "亘") ⟫ʷ
wl0205 c4 = lw4 c4 (ℓ "二于乐于二乐") (ℓ "亘") tt tt Eq.refl

wl0206 : Base 4 → ⟪ (ℓ "个亙") ⟫ʷ ≈ ⟪ (ℓ "亙个交") ⟫ʷ
wl0206 c4 = lw4 c4 (ℓ "个亙") (ℓ "亙个交") tt tt Eq.refl

wl0207 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "乢之乣之乎") ⟫ʷ
wl0207 c4 = lw4 c4 (ℓ "交") (ℓ "乢之乣之乎") tt tt Eq.refl

wl0208 : Base 4 → ⟪ (ℓ "並个个") ⟫ʷ ≈ ⟪ (ℓ "並") ⟫ʷ
wl0208 c4 = lw2 c4 (ℓ "並个个") (ℓ "並") tt tt Eq.refl

wl0209 : Base 4 → ⟪ (ℓ "交亙") ⟫ʷ ≈ ⟪ (ℓ "亙交") ⟫ʷ
wl0209 c4 = lw4 c4 (ℓ "交亙") (ℓ "亙交") tt tt Eq.refl

wl0210 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "並交並") ⟫ʷ
wl0210 c4 = lw0 c4 (ℓ "交") (ℓ "並交並") tt tt Eq.refl

wl0211 : Base 4 → ⟪ (ℓ "亲並") ⟫ʷ ≈ ⟪ (ℓ "並书亲") ⟫ʷ
wl0211 c4 = lw0 c4 (ℓ "亲並") (ℓ "並书亲") tt tt Eq.refl

wl0212 : Base 4 → ⟪ (ℓ "乎书") ⟫ʷ ≈ ⟪ (ℓ "书乇交乎") ⟫ʷ
wl0212 c4 = lw4 c4 (ℓ "乎书") (ℓ "书乇交乎") tt tt Eq.refl

wl0213 : Base 4 → ⟪ (ℓ "书亲") ⟫ʷ ≈ ⟪ (ℓ "亲书") ⟫ʷ
wl0213 c4 = lw0 c4 (ℓ "书亲") (ℓ "亲书") tt tt Eq.refl

wl0214 : Base 4 → ⟪ (ℓ "乇亲") ⟫ʷ ≈ ⟪ (ℓ "亲乇") ⟫ʷ
wl0214 c4 = lw0 c4 (ℓ "乇亲") (ℓ "亲乇") tt tt Eq.refl

wl0215 : Base 4 → ⟪ (ℓ "交亨亲") ⟫ʷ ≈ ⟪ (ℓ "亲交") ⟫ʷ
wl0215 c4 = lw0 c4 (ℓ "交亨亲") (ℓ "亲交") tt tt Eq.refl

wl0216 : Base 4 → ⟪ (ℓ "並乇交亨") ⟫ʷ ≈ ⟪ (ℓ "並书书乇交亨") ⟫ʷ
wl0216 c4 = lw0 c4 (ℓ "並乇交亨") (ℓ "並书书乇交亨") tt tt Eq.refl

wl0217 : Base 4 → ⟪ (ℓ "丞乹书乺书乩丟") ⟫ʷ ≈ ⟪ (ℓ "亲") ⟫ʷ
wl0217 c4 = lw0 c4 (ℓ "丞乹书乺书乩丟") (ℓ "亲") tt tt Eq.refl

wl0218 : Base 4 → ⟪ (ℓ "交乇交亨亲乎") ⟫ʷ ≈ ⟪ (ℓ "亲乇乎亨") ⟫ʷ
wl0218 c4 = lw0 c4 (ℓ "交乇交亨亲乎") (ℓ "亲乇乎亨") tt tt Eq.refl

wl0219 : Base 4 → ⟪ (ℓ "乏亙") ⟫ʷ ≈ ⟪ (ℓ "亙乏") ⟫ʷ
wl0219 c4 = lw4 c4 (ℓ "乏亙") (ℓ "亙乏") tt tt Eq.refl

wl0220 : Base 4 → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "乩乙乪乙乇") ⟫ʷ
wl0220 c4 = lw0 c4 (ℓ "亨") (ℓ "乩乙乪乙乇") tt tt Eq.refl

wl0221 : Base 4 → ⟪ (ℓ "乇亙") ⟫ʷ ≈ ⟪ (ℓ "亙乇") ⟫ʷ
wl0221 c4 = lw4 c4 (ℓ "乇亙") (ℓ "亙乇") tt tt Eq.refl

wl0222 : Base 4 → ⟪ (ℓ "乎亙") ⟫ʷ ≈ ⟪ (ℓ "亙乎") ⟫ʷ
wl0222 c4 = lw4 c4 (ℓ "乎亙") (ℓ "亙乎") tt tt Eq.refl

wl0223 : Base 4 → ⟪ (ℓ "亨亲乇乎亨") ⟫ʷ ≈ ⟪ (ℓ "亲乇乎") ⟫ʷ
wl0223 c4 = lw0 c4 (ℓ "亨亲乇乎亨") (ℓ "亲乇乎") tt tt Eq.refl

wl0224 : Base 4 → ⟪ (ℓ "乇") ⟫ʷ ≈ ⟪ (ℓ "亲乇乎亨亲乏亲乎亲乏") ⟫ʷ
wl0224 c4 = lw0 c4 (ℓ "乇") (ℓ "亲乇乎亨亲乏亲乎亲乏") tt tt Eq.refl

wl0225 : Base 4 → ⟪ (ℓ "亐丯") ⟫ʷ ≈ ⟪ (ℓ "丯亐") ⟫ʷ
wl0225 c4 = lw4 c4 (ℓ "亐丯") (ℓ "丯亐") tt tt Eq.refl

wl0226 : Base 4 → ⟪ (ℓ "丌亐不") ⟫ʷ ≈ ⟪ (ℓ "云") ⟫ʷ
wl0226 c4 = lw4 c4 (ℓ "丌亐不") (ℓ "云") tt tt Eq.refl

wl0227 : Base 4 → ⟪ (ℓ "乏上云下") ⟫ʷ ≈ ⟪ (ℓ "云亐") ⟫ʷ
wl0227 c4 = lw4 c4 (ℓ "乏上云下") (ℓ "云亐") tt tt Eq.refl

wl0228 : Base 4 → ⟪ (ℓ "乏乪") ⟫ʷ ≈ ⟪ (ℓ "乪乏") ⟫ʷ
wl0228 c4 = lw0 c4 (ℓ "乏乪") (ℓ "乪乏") tt tt Eq.refl

wl0229 : Base 4 → ⟪ (ℓ "云云") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0229 c4 = lw4 c4 (ℓ "云云") [] tt tt Eq.refl

wl0230 : Base 4 → ⟪ (ℓ "亐亐") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0230 c4 = lw4 c4 (ℓ "亐亐") [] tt tt Eq.refl

wl0231 : Base 4 → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "亘亚义亚亘义") ⟫ʷ
wl0231 c4 = lw4 c4 (ℓ "亐") (ℓ "亘亚义亚亘义") tt tt Eq.refl

wl0232 : Base 4 → ⟪ (ℓ "丱云") ⟫ʷ ≈ ⟪ (ℓ "云丱交") ⟫ʷ
wl0232 c4 = lw4 c4 (ℓ "丱云") (ℓ "云丱交") tt tt Eq.refl

wl0233 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "乎书乏书乇") ⟫ʷ
wl0233 c4 = lw4 c4 (ℓ "交") (ℓ "乎书乏书乇") tt tt Eq.refl

wl0234 : Base 4 → ⟪ (ℓ "交云") ⟫ʷ ≈ ⟪ (ℓ "云交") ⟫ʷ
wl0234 c4 = lw4 c4 (ℓ "交云") (ℓ "云交") tt tt Eq.refl

wl0235 : Base 4 → ⟪ (ℓ "亭並") ⟫ʷ ≈ ⟪ (ℓ "並乳亭") ⟫ʷ
wl0235 c4 = lw0 c4 (ℓ "亭並") (ℓ "並乳亭") tt tt Eq.refl

wl0236 : Base 4 → ⟪ (ℓ "乇乳") ⟫ʷ ≈ ⟪ (ℓ "乳乢交乇") ⟫ʷ
wl0236 c4 = lw4 c4 (ℓ "乇乳") (ℓ "乳乢交乇") tt tt Eq.refl

wl0237 : Base 4 → ⟪ (ℓ "乳亭") ⟫ʷ ≈ ⟪ (ℓ "亭乳") ⟫ʷ
wl0237 c4 = lw0 c4 (ℓ "乳亭") (ℓ "亭乳") tt tt Eq.refl

wl0238 : Base 4 → ⟪ (ℓ "乢亭") ⟫ʷ ≈ ⟪ (ℓ "亭乢") ⟫ʷ
wl0238 c4 = lw0 c4 (ℓ "乢亭") (ℓ "亭乢") tt tt Eq.refl

wl0239 : Base 4 → ⟪ (ℓ "交亰亭") ⟫ʷ ≈ ⟪ (ℓ "亭交") ⟫ʷ
wl0239 c4 = lw0 c4 (ℓ "交亰亭") (ℓ "亭交") tt tt Eq.refl

wl0240 : Base 4 → ⟪ (ℓ "並乢交亰") ⟫ʷ ≈ ⟪ (ℓ "並乳乳乢交亰") ⟫ʷ
wl0240 c4 = lw0 c4 (ℓ "並乢交亰") (ℓ "並乳乳乢交亰") tt tt Eq.refl

wl0241 : Base 4 → ⟪ (ℓ "丒乹乒乺乒乕专") ⟫ʷ ≈ ⟪ (ℓ "亭") ⟫ʷ
wl0241 c4 = lw0 c4 (ℓ "丒乹乒乺乒乕专") (ℓ "亭") tt tt Eq.refl

wl0242 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "乢乒乣乒乇") ⟫ʷ
wl0242 c4 = lw4 c4 (ℓ "交") (ℓ "乢乒乣乒乇") tt tt Eq.refl

wl0243 : Base 4 → ⟪ (ℓ "交乢交亰亭乇") ⟫ʷ ≈ ⟪ (ℓ "亭乇乢亰") ⟫ʷ
wl0243 c4 = lw0 c4 (ℓ "交乢交亰亭乇") (ℓ "亭乇乢亰") tt tt Eq.refl

wl0244 : Base 4 → ⟪ (ℓ "么云") ⟫ʷ ≈ ⟪ (ℓ "云么") ⟫ʷ
wl0244 c4 = lw4 c4 (ℓ "么云") (ℓ "云么") tt tt Eq.refl

wl0245 : Base 4 → ⟪ (ℓ "亰") ⟫ʷ ≈ ⟪ (ℓ "乹乭乺乭乢") ⟫ʷ
wl0245 c4 = lw0 c4 (ℓ "亰") (ℓ "乹乭乺乭乢") tt tt Eq.refl

wl0246 : Base 4 → ⟪ (ℓ "乢云") ⟫ʷ ≈ ⟪ (ℓ "云乢") ⟫ʷ
wl0246 c4 = lw4 c4 (ℓ "乢云") (ℓ "云乢") tt tt Eq.refl
