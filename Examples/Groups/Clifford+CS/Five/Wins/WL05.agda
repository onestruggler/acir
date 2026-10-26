------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WL05 where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

wl0930 : Base 4 → ⟪ (ℓ "二亏") ⟫ʷ ≈ ⟪ (ℓ "亏二个") ⟫ʷ
wl0930 c4 = lw4 c4 (ℓ "二亏") (ℓ "亏二个") tt tt Eq.refl

wl0931 : Base 4 → ⟪ (ℓ "二个亏二") ⟫ʷ ≈ ⟪ (ℓ "亏") ⟫ʷ
wl0931 c4 = lw4 c4 (ℓ "二个亏二") (ℓ "亏") tt tt Eq.refl

wl0932 : Base 4 → ⟪ (ℓ "亰乻亱") ⟫ʷ ≈ ⟪ (ℓ "亱亰") ⟫ʷ
wl0932 c4 = lw0 c4 (ℓ "亰乻亱") (ℓ "亱亰") tt tt Eq.refl

wl0933 : Base 4 → ⟪ (ℓ "亰乻") ⟫ʷ ≈ ⟪ (ℓ "亱亰亱") ⟫ʷ
wl0933 c4 = lw0 c4 (ℓ "亰乻") (ℓ "亱亰亱") tt tt Eq.refl

wl0934 : Base 4 → ⟪ (ℓ "亰") ⟫ʷ ≈ ⟪ (ℓ "乻亰乻") ⟫ʷ
wl0934 c4 = lw0 c4 (ℓ "亰") (ℓ "乻亰乻") tt tt Eq.refl

wl0935 : Base 4 → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "交产丸产交丸") ⟫ʷ
wl0935 c4 = lw4 c4 (ℓ "二") (ℓ "交产丸产交丸") tt tt Eq.refl

wl0936 : Base 4 → ⟪ (ℓ "亰亱") ⟫ʷ ≈ ⟪ (ℓ "亱亰乻") ⟫ʷ
wl0936 c4 = lw0 c4 (ℓ "亰亱") (ℓ "亱亰乻") tt tt Eq.refl

wl0937 : Base 4 → ⟪ (ℓ "亰乻亱亰") ⟫ʷ ≈ ⟪ (ℓ "亱") ⟫ʷ
wl0937 c4 = lw0 c4 (ℓ "亰乻亱亰") (ℓ "亱") tt tt Eq.refl

wl0938 : Base 4 → ⟪ (ℓ "亃亱") ⟫ʷ ≈ ⟪ (ℓ "亱亃") ⟫ʷ
wl0938 c4 = lw0 c4 (ℓ "亃亱") (ℓ "亱亃") tt tt Eq.refl

wl0939 : Base 4 → ⟪ (ℓ "乙亱") ⟫ʷ ≈ ⟪ (ℓ "亱乙亦") ⟫ʷ
wl0939 c4 = lw0 c4 (ℓ "乙亱") (ℓ "亱乙亦") tt tt Eq.refl

wl0940 : Base 4 → ⟪ (ℓ "二亦亐") ⟫ʷ ≈ ⟪ (ℓ "亦二") ⟫ʷ
wl0940 c4 = lw4 c4 (ℓ "二亦亐") (ℓ "亦二") tt tt Eq.refl

wl0941 : Base 4 → ⟪ (ℓ "乳亱") ⟫ʷ ≈ ⟪ (ℓ "亱乳") ⟫ʷ
wl0941 c4 = lw0 c4 (ℓ "乳亱") (ℓ "亱乳") tt tt Eq.refl

wl0942 : Base 4 → ⟪ (ℓ "亦亱") ⟫ʷ ≈ ⟪ (ℓ "亱亦") ⟫ʷ
wl0942 c4 = lw0 c4 (ℓ "亦亱") (ℓ "亱亦") tt tt Eq.refl

wl0943 : Base 4 → ⟪ (ℓ "乙亦亦") ⟫ʷ ≈ ⟪ (ℓ "乙") ⟫ʷ
wl0943 c4 = lw0 c4 (ℓ "乙亦亦") (ℓ "乙") tt tt Eq.refl

wl0944 : Base 4 → ⟪ (ℓ "乙亦") ⟫ʷ ≈ ⟪ (ℓ "亦乙") ⟫ʷ
wl0944 c4 = lw0 c4 (ℓ "乙亦") (ℓ "亦乙") tt tt Eq.refl

wl0945 : Base 4 → ⟪ (ℓ "二亦") ⟫ʷ ≈ ⟪ (ℓ "亦二亐") ⟫ʷ
wl0945 c4 = lw4 c4 (ℓ "二亦") (ℓ "亦二亐") tt tt Eq.refl

wl0946 : Base 4 → ⟪ (ℓ "亃亦") ⟫ʷ ≈ ⟪ (ℓ "亦亃亱") ⟫ʷ
wl0946 c4 = lw0 c4 (ℓ "亃亦") (ℓ "亦亃亱") tt tt Eq.refl

wl0947 : Base 4 → ⟪ (ℓ "乽亦") ⟫ʷ ≈ ⟪ (ℓ "亦乽") ⟫ʷ
wl0947 c4 = lw0 c4 (ℓ "乽亦") (ℓ "亦乽") tt tt Eq.refl

wl0948 : Base 4 → ⟪ (ℓ "亃亱亱") ⟫ʷ ≈ ⟪ (ℓ "亃") ⟫ʷ
wl0948 c4 = lw0 c4 (ℓ "亃亱亱") (ℓ "亃") tt tt Eq.refl

wl0949 : Base 4 → ⟪ (ℓ "二个亏") ⟫ʷ ≈ ⟪ (ℓ "亏二") ⟫ʷ
wl0949 c4 = lw4 c4 (ℓ "二个亏") (ℓ "亏二") tt tt Eq.refl

wl0950 : Base 4 → ⟪ (ℓ "二个") ⟫ʷ ≈ ⟪ (ℓ "亏二亏") ⟫ʷ
wl0950 c4 = lw4 c4 (ℓ "二个") (ℓ "亏二亏") tt tt Eq.refl

wl0951 : Base 4 → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "个二个") ⟫ʷ
wl0951 c4 = lw4 c4 (ℓ "二") (ℓ "个二个") tt tt Eq.refl

wl0952 : Base 4 → ⟪ (ℓ "丘乎也乏也乢丙") ⟫ʷ ≈ ⟪ (ℓ "亦") ⟫ʷ
wl0952 c4 = lw4 c4 (ℓ "丘乎也乏也乢丙") (ℓ "亦") tt tt Eq.refl

wl0953 : Base 4 → ⟪ (ℓ "亦亐亐") ⟫ʷ ≈ ⟪ (ℓ "亦") ⟫ʷ
wl0953 c4 = lw4 c4 (ℓ "亦亐亐") (ℓ "亦") tt tt Eq.refl

wl0954 : Base 4 → ⟪ (ℓ "京亦") ⟫ʷ ≈ ⟪ (ℓ "亦京") ⟫ʷ
wl0954 c4 = lw0 c4 (ℓ "京亦") (ℓ "亦京") tt tt Eq.refl

wl0955 : Base 4 → ⟪ (ℓ "为亏") ⟫ʷ ≈ ⟪ (ℓ "亏为") ⟫ʷ
wl0955 c4 = lw4 c4 (ℓ "为亏") (ℓ "亏为") tt tt Eq.refl

wl0956 : Base 4 → ⟪ (ℓ "买亏") ⟫ʷ ≈ ⟪ (ℓ "亏买亦") ⟫ʷ
wl0956 c4 = lw4 c4 (ℓ "买亏") (ℓ "亏买亦") tt tt Eq.refl

wl0957 : Base 4 → ⟪ (ℓ "亰亦京") ⟫ʷ ≈ ⟪ (ℓ "亦亰") ⟫ʷ
wl0957 c4 = lw0 c4 (ℓ "亰亦京") (ℓ "亦亰") tt tt Eq.refl

wl0958 : Base 4 → ⟪ (ℓ "乒亏") ⟫ʷ ≈ ⟪ (ℓ "亏乒") ⟫ʷ
wl0958 c4 = lw4 c4 (ℓ "乒亏") (ℓ "亏乒") tt tt Eq.refl

wl0959 : Base 4 → ⟪ (ℓ "买亦亦") ⟫ʷ ≈ ⟪ (ℓ "买") ⟫ʷ
wl0959 c4 = lw4 c4 (ℓ "买亦亦") (ℓ "买") tt tt Eq.refl

wl0960 : Base 4 → ⟪ (ℓ "京亰") ⟫ʷ ≈ ⟪ (ℓ "亰京") ⟫ʷ
wl0960 c4 = lw0 c4 (ℓ "京亰") (ℓ "亰京") tt tt Eq.refl

wl0961 : Base 4 → ⟪ (ℓ "为买为") ⟫ʷ ≈ ⟪ (ℓ "丹") ⟫ʷ
wl0961 c4 = lw4 c4 (ℓ "为买为") (ℓ "丹") tt tt Eq.refl

wl0962 : Base 4 → ⟪ (ℓ "丹亏") ⟫ʷ ≈ ⟪ (ℓ "亦丹") ⟫ʷ
wl0962 c4 = lw4 c4 (ℓ "丹亏") (ℓ "亦丹") tt tt Eq.refl

wl0963 : Base 4 → ⟪ (ℓ "丹亥") ⟫ʷ ≈ ⟪ (ℓ "于丹") ⟫ʷ
wl0963 c4 = lw4 c4 (ℓ "丹亥") (ℓ "于丹") tt tt Eq.refl

wl0964 : Base 4 → ⟪ (ℓ "乇亦") ⟫ʷ ≈ ⟪ (ℓ "亦乇乎交") ⟫ʷ
wl0964 c4 = lw4 c4 (ℓ "乇亦") (ℓ "亦乇乎交") tt tt Eq.refl

wl0965 : Base 4 → ⟪ (ℓ "交亦") ⟫ʷ ≈ ⟪ (ℓ "亦乐交") ⟫ʷ
wl0965 c4 = lw4 c4 (ℓ "交亦") (ℓ "亦乐交") tt tt Eq.refl

wl0966 : Base 4 → ⟪ (ℓ "乎亦") ⟫ʷ ≈ ⟪ (ℓ "亦乎") ⟫ʷ
wl0966 c4 = lw4 c4 (ℓ "乎亦") (ℓ "亦乎") tt tt Eq.refl

wl0967 : Base 4 → ⟪ (ℓ "乇乎交乎乐交") ⟫ʷ ≈ ⟪ (ℓ "乇") ⟫ʷ
wl0967 c4 = lw4 c4 (ℓ "乇乎交乎乐交") (ℓ "乇") tt tt Eq.refl

wl0968 : Base 4 → ⟪ (ℓ "么亦") ⟫ʷ ≈ ⟪ (ℓ "亦么乏交") ⟫ʷ
wl0968 c4 = lw4 c4 (ℓ "么亦") (ℓ "亦么乏交") tt tt Eq.refl

wl0969 : Base 4 → ⟪ (ℓ "乏亦") ⟫ʷ ≈ ⟪ (ℓ "亦乏") ⟫ʷ
wl0969 c4 = lw4 c4 (ℓ "乏亦") (ℓ "亦乏") tt tt Eq.refl

wl0970 : Base 4 → ⟪ (ℓ "么乏交乏乐交") ⟫ʷ ≈ ⟪ (ℓ "么") ⟫ʷ
wl0970 c4 = lw4 c4 (ℓ "么乏交乏乐交") (ℓ "么") tt tt Eq.refl

wl0971 : Base 4 → ⟪ (ℓ "乐交亦") ⟫ʷ ≈ ⟪ (ℓ "亦交") ⟫ʷ
wl0971 c4 = lw4 c4 (ℓ "乐交亦") (ℓ "亦交") tt tt Eq.refl

wl0972 : Base 4 → ⟪ (ℓ "交亨亮") ⟫ʷ ≈ ⟪ (ℓ "亨亮交亨") ⟫ʷ
wl0972 c4 = lw0 c4 (ℓ "交亨亮") (ℓ "亨亮交亨") tt tt Eq.refl

wl0973 : Base 4 → ⟪ (ℓ "交亨亨亮") ⟫ʷ ≈ ⟪ (ℓ "亨亮交") ⟫ʷ
wl0973 c4 = lw0 c4 (ℓ "交亨亨亮") (ℓ "亨亮交") tt tt Eq.refl

wl0974 : Base 4 → ⟪ (ℓ "亨亮") ⟫ʷ ≈ ⟪ (ℓ "亮亨") ⟫ʷ
wl0974 c4 = lw0 c4 (ℓ "亨亮") (ℓ "亮亨") tt tt Eq.refl

wl0975 : Base 4 → ⟪ (ℓ "乳亭並") ⟫ʷ ≈ ⟪ (ℓ "並亭") ⟫ʷ
wl0975 c4 = lw0 c4 (ℓ "乳亭並") (ℓ "並亭") tt tt Eq.refl

wl0976 : Base 4 → ⟪ (ℓ "乳乶亦") ⟫ʷ ≈ ⟪ (ℓ "亦乳") ⟫ʷ
wl0976 c4 = lw4 c4 (ℓ "乳乶亦") (ℓ "亦乳") tt tt Eq.refl

wl0977 : Base 4 → ⟪ (ℓ "亭亱亦") ⟫ʷ ≈ ⟪ (ℓ "亦亭") ⟫ʷ
wl0977 c4 = lw0 c4 (ℓ "亭亱亦") (ℓ "亦亭") tt tt Eq.refl

wl0978 : Base 4 → ⟪ (ℓ "乳乶乶") ⟫ʷ ≈ ⟪ (ℓ "乳") ⟫ʷ
wl0978 c4 = lw4 c4 (ℓ "乳乶乶") (ℓ "乳") tt tt Eq.refl

wl0979 : Base 4 → ⟪ (ℓ "亭亱亱") ⟫ʷ ≈ ⟪ (ℓ "亭") ⟫ʷ
wl0979 c4 = lw0 c4 (ℓ "亭亱亱") (ℓ "亭") tt tt Eq.refl

wl0980 : Base 4 → ⟪ (ℓ "乇並") ⟫ʷ ≈ ⟪ (ℓ "並乇") ⟫ʷ
wl0980 c4 = lw0 c4 (ℓ "乇並") (ℓ "並乇") tt tt Eq.refl

wl0981 : Base 4 → ⟪ (ℓ "丷乇") ⟫ʷ ≈ ⟪ (ℓ "乇丷") ⟫ʷ
wl0981 c4 = lw4 c4 (ℓ "丷乇") (ℓ "乇丷") tt tt Eq.refl

wl0982 : Base 4 → ⟪ (ℓ "乇亮") ⟫ʷ ≈ ⟪ (ℓ "亮乇") ⟫ʷ
wl0982 c4 = lw0 c4 (ℓ "乇亮") (ℓ "亮乇") tt tt Eq.refl

wl0983 : Base 4 → ⟪ (ℓ "丶乇") ⟫ʷ ≈ ⟪ (ℓ "乇丶") ⟫ʷ
wl0983 c4 = lw4 c4 (ℓ "丶乇") (ℓ "乇丶") tt tt Eq.refl

wl0984 : Base 4 → ⟪ (ℓ "么並") ⟫ʷ ≈ ⟪ (ℓ "並么") ⟫ʷ
wl0984 c4 = lw0 c4 (ℓ "么並") (ℓ "並么") tt tt Eq.refl

wl0985 : Base 4 → ⟪ (ℓ "么亮") ⟫ʷ ≈ ⟪ (ℓ "亮么") ⟫ʷ
wl0985 c4 = lw0 c4 (ℓ "么亮") (ℓ "亮么") tt tt Eq.refl

wl0986 : Base 4 → ⟪ (ℓ "丶么") ⟫ʷ ≈ ⟪ (ℓ "么丶") ⟫ʷ
wl0986 c4 = lw4 c4 (ℓ "丶么") (ℓ "么丶") tt tt Eq.refl

wl0987 : Base 4 → ⟪ (ℓ "乒亙") ⟫ʷ ≈ ⟪ (ℓ "亙乒亍") ⟫ʷ
wl0987 c4 = lw4 c4 (ℓ "乒亙") (ℓ "亙乒亍") tt tt Eq.refl

wl0988 : Base 4 → ⟪ (ℓ "乒亍亍") ⟫ʷ ≈ ⟪ (ℓ "乒") ⟫ʷ
wl0988 c4 = lw4 c4 (ℓ "乒亍亍") (ℓ "乒") tt tt Eq.refl

wl0989 : Base 4 → ⟪ (ℓ "乑亙") ⟫ʷ ≈ ⟪ (ℓ "亍乑") ⟫ʷ
wl0989 c4 = lw4 c4 (ℓ "乑亙") (ℓ "亍乑") tt tt Eq.refl

wl0990 : Base 4 → ⟪ (ℓ "乑亏") ⟫ʷ ≈ ⟪ (ℓ "亚乑") ⟫ʷ
wl0990 c4 = lw4 c4 (ℓ "乑亏") (ℓ "亚乑") tt tt Eq.refl

wl0991 : Base 4 → ⟪ (ℓ "二交亙") ⟫ʷ ≈ ⟪ (ℓ "亙二") ⟫ʷ
wl0991 c4 = lw4 c4 (ℓ "二交亙") (ℓ "亙二") tt tt Eq.refl

wl0992 : Base 4 → ⟪ (ℓ "二乏") ⟫ʷ ≈ ⟪ (ℓ "乏二") ⟫ʷ
wl0992 c4 = lw4 c4 (ℓ "二乏") (ℓ "乏二") tt tt Eq.refl

wl0993 : Base 4 → ⟪ (ℓ "二並") ⟫ʷ ≈ ⟪ (ℓ "並二") ⟫ʷ
wl0993 c4 = lw3 c4 (ℓ "二並") (ℓ "並二") tt tt Eq.refl

wl0994 : Base 4 → ⟪ (ℓ "之亪並") ⟫ʷ ≈ ⟪ (ℓ "並亪") ⟫ʷ
wl0994 c4 = lw0 c4 (ℓ "之亪並") (ℓ "並亪") tt tt Eq.refl

wl0995 : Base 4 → ⟪ (ℓ "之亪亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏之亪") ⟫ʷ
wl0995 c4 = lw0 c4 (ℓ "之亪亲乎亲乏") (ℓ "亲乎亲乏之亪") tt tt Eq.refl

wl0996 : Base 4 → ⟪ (ℓ "亪並") ⟫ʷ ≈ ⟪ (ℓ "並之亪") ⟫ʷ
wl0996 c4 = lw0 c4 (ℓ "亪並") (ℓ "並之亪") tt tt Eq.refl

wl0997 : Base 4 → ⟪ (ℓ "丯並") ⟫ʷ ≈ ⟪ (ℓ "並丯") ⟫ʷ
wl0997 c4 = lw3 c4 (ℓ "丯並") (ℓ "並丯") tt tt Eq.refl

wl0998 : Base 4 → ⟪ (ℓ "丰並") ⟫ʷ ≈ ⟪ (ℓ "並丰") ⟫ʷ
wl0998 c4 = lw3 c4 (ℓ "丰並") (ℓ "並丰") tt tt Eq.refl

wl0999 : Base 4 → ⟪ (ℓ "交亨亲乎亨亲乏並") ⟫ʷ ≈ ⟪ (ℓ "亨亲乎亨亲乏並交") ⟫ʷ
wl0999 c4 = lw0 c4 (ℓ "交亨亲乎亨亲乏並") (ℓ "亨亲乎亨亲乏並交") tt tt Eq.refl

wl1000 : Base 4 → ⟪ (ℓ "亨亲乎") ⟫ʷ ≈ ⟪ (ℓ "亲乎亨") ⟫ʷ
wl1000 c4 = lw0 c4 (ℓ "亨亲乎") (ℓ "亲乎亨") tt tt Eq.refl

wl1001 : Base 4 → ⟪ (ℓ "书亲亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏书亲") ⟫ʷ
wl1001 c4 = lw0 c4 (ℓ "书亲亲乎亲乏") (ℓ "亲乎亲乏书亲") tt tt Eq.refl

wl1002 : Base 4 → ⟪ (ℓ "乜书亙") ⟫ʷ ≈ ⟪ (ℓ "亙书") ⟫ʷ
wl1002 c4 = lw4 c4 (ℓ "乜书亙") (ℓ "亙书") tt tt Eq.refl

wl1003 : Base 4 → ⟪ (ℓ "乜亙") ⟫ʷ ≈ ⟪ (ℓ "亙乜") ⟫ʷ
wl1003 c4 = lw4 c4 (ℓ "乜亙") (ℓ "亙乜") tt tt Eq.refl

wl1004 : Base 4 → ⟪ (ℓ "亨书亨亲") ⟫ʷ ≈ ⟪ (ℓ "书亲") ⟫ʷ
wl1004 c4 = lw0 c4 (ℓ "亨书亨亲") (ℓ "书亲") tt tt Eq.refl

wl1005 : Base 4 → ⟪ (ℓ "乎亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏乎") ⟫ʷ
wl1005 c4 = lw0 c4 (ℓ "乎亲乎亲乏") (ℓ "亲乎亲乏乎") tt tt Eq.refl

wl1006 : Base 4 → ⟪ (ℓ "乏亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏乏") ⟫ʷ
wl1006 c4 = lw0 c4 (ℓ "乏亲乎亲乏") (ℓ "亲乎亲乏乏") tt tt Eq.refl

wl1007 : Base 4 → ⟪ (ℓ "亐亙") ⟫ʷ ≈ ⟪ (ℓ "亙亐交") ⟫ʷ
wl1007 c4 = lw4 c4 (ℓ "亐亙") (ℓ "亙亐交") tt tt Eq.refl

wl1008 : Base 4 → ⟪ (ℓ "交乽") ⟫ʷ ≈ ⟪ (ℓ "乽交") ⟫ʷ
wl1008 c4 = lw0 c4 (ℓ "交乽") (ℓ "乽交") tt tt Eq.refl

wl1009 : Base 4 → ⟪ (ℓ "交亨交亨交") ⟫ʷ ≈ ⟪ (ℓ "交") ⟫ʷ
wl1009 c4 = lw0 c4 (ℓ "交亨交亨交") (ℓ "交") tt tt Eq.refl

wl1010 : Base 4 → ⟪ (ℓ "交亲亨乎亲亨乏並") ⟫ʷ ≈ ⟪ (ℓ "亲亨乎亲亨乏並交") ⟫ʷ
wl1010 c4 = lw0 c4 (ℓ "交亲亨乎亲亨乏並") (ℓ "亲亨乎亲亨乏並交") tt tt Eq.refl

wl1011 : Base 4 → ⟪ (ℓ "亨乎亲") ⟫ʷ ≈ ⟪ (ℓ "乎亲亨") ⟫ʷ
wl1011 c4 = lw0 c4 (ℓ "亨乎亲") (ℓ "乎亲亨") tt tt Eq.refl

wl1012 : Base 4 → ⟪ (ℓ "乳亭亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏乳亭") ⟫ʷ
wl1012 c4 = lw0 c4 (ℓ "乳亭亲乎亲乏") (ℓ "亲乎亲乏乳亭") tt tt Eq.refl

wl1013 : Base 4 → ⟪ (ℓ "丒乹乙乺乙乎专") ⟫ʷ ≈ ⟪ (ℓ "亭") ⟫ʷ
wl1013 c4 = lw0 c4 (ℓ "丒乹乙乺乙乎专") (ℓ "亭") tt tt Eq.refl

wl1014 : Base 4 → ⟪ (ℓ "专亙") ⟫ʷ ≈ ⟪ (ℓ "亙专") ⟫ʷ
wl1014 c4 = lw4 c4 (ℓ "专亙") (ℓ "亙专") tt tt Eq.refl

wl1015 : Base 4 → ⟪ (ℓ "乇亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏乇") ⟫ʷ
wl1015 c4 = lw0 c4 (ℓ "乇亲乎亲乏") (ℓ "亲乎亲乏乇") tt tt Eq.refl

wl1016 : Base 4 → ⟪ (ℓ "么亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏么") ⟫ʷ
wl1016 c4 = lw0 c4 (ℓ "么亲乎亲乏") (ℓ "亲乎亲乏么") tt tt Eq.refl

wl1017 : Base 4 → ⟪ (ℓ "么亙") ⟫ʷ ≈ ⟪ (ℓ "亙么") ⟫ʷ
wl1017 c4 = lw4 c4 (ℓ "么亙") (ℓ "亙么") tt tt Eq.refl

wl1018 : Base 4 → ⟪ (ℓ "书云") ⟫ʷ ≈ ⟪ (ℓ "云书亍") ⟫ʷ
wl1018 c4 = lw4 c4 (ℓ "书云") (ℓ "云书亍") tt tt Eq.refl

wl1019 : Base 4 → ⟪ (ℓ "书亍亍") ⟫ʷ ≈ ⟪ (ℓ "书") ⟫ʷ
wl1019 c4 = lw4 c4 (ℓ "书亍亍") (ℓ "书") tt tt Eq.refl

wl1020 : Base 4 → ⟪ (ℓ "乶书乶") ⟫ʷ ≈ ⟪ (ℓ "乥") ⟫ʷ
wl1020 c4 = lw4 c4 (ℓ "乶书乶") (ℓ "乥") tt tt Eq.refl

wl1021 : Base 4 → ⟪ (ℓ "京乶") ⟫ʷ ≈ ⟪ (ℓ "乶京") ⟫ʷ
wl1021 c4 = lw0 c4 (ℓ "京乶") (ℓ "乶京") tt tt Eq.refl

wl1022 : Base 4 → ⟪ (ℓ "京亨京亨京") ⟫ʷ ≈ ⟪ (ℓ "京") ⟫ʷ
wl1022 c4 = lw0 c4 (ℓ "京亨京亨京") (ℓ "京") tt tt Eq.refl

wl1023 : Base 4 → ⟪ (ℓ "乥云") ⟫ʷ ≈ ⟪ (ℓ "亍乥") ⟫ʷ
wl1023 c4 = lw4 c4 (ℓ "乥云") (ℓ "亍乥") tt tt Eq.refl

wl1024 : Base 4 → ⟪ (ℓ "乥于") ⟫ʷ ≈ ⟪ (ℓ "互乥") ⟫ʷ
wl1024 c4 = lw4 c4 (ℓ "乥于") (ℓ "互乥") tt tt Eq.refl

wl1025 : Base 4 → ⟪ (ℓ "亭亦") ⟫ʷ ≈ ⟪ (ℓ "亦亭亱") ⟫ʷ
wl1025 c4 = lw0 c4 (ℓ "亭亦") (ℓ "亦亭亱") tt tt Eq.refl

wl1026 : Base 4 → ⟪ (ℓ "乐亐云") ⟫ʷ ≈ ⟪ (ℓ "云亐") ⟫ʷ
wl1026 c4 = lw4 c4 (ℓ "乐亐云") (ℓ "云亐") tt tt Eq.refl

wl1027 : Base 4 → ⟪ (ℓ "乒亮亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么乒亮") ⟫ʷ
wl1027 c4 = lw0 c4 (ℓ "乒亮亭乇亭么") (ℓ "亭乇亭么乒亮") tt tt Eq.refl

wl1028 : Base 4 → ⟪ (ℓ "乄乒云") ⟫ʷ ≈ ⟪ (ℓ "云乒") ⟫ʷ
wl1028 c4 = lw4 c4 (ℓ "乄乒云") (ℓ "云乒") tt tt Eq.refl

wl1029 : Base 4 → ⟪ (ℓ "乄云") ⟫ʷ ≈ ⟪ (ℓ "云乄") ⟫ʷ
wl1029 c4 = lw4 c4 (ℓ "乄云") (ℓ "云乄") tt tt Eq.refl

wl1030 : Base 4 → ⟪ (ℓ "亨乒亨亮") ⟫ʷ ≈ ⟪ (ℓ "乒亮") ⟫ʷ
wl1030 c4 = lw0 c4 (ℓ "亨乒亨亮") (ℓ "乒亮") tt tt Eq.refl

wl1031 : Base 4 → ⟪ (ℓ "交亭亰乇亭亰么並") ⟫ʷ ≈ ⟪ (ℓ "亭亰乇亭亰么並交") ⟫ʷ
wl1031 c4 = lw0 c4 (ℓ "交亭亰乇亭亰么並") (ℓ "亭亰乇亭亰么並交") tt tt Eq.refl

wl1032 : Base 4 → ⟪ (ℓ "亰乇亭") ⟫ʷ ≈ ⟪ (ℓ "乇亭亰") ⟫ʷ
wl1032 c4 = lw0 c4 (ℓ "亰乇亭") (ℓ "乇亭亰") tt tt Eq.refl

wl1033 : Base 4 → ⟪ (ℓ "书亲亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么书亲") ⟫ʷ
wl1033 c4 = lw0 c4 (ℓ "书亲亭乇亭么") (ℓ "亭乇亭么书亲") tt tt Eq.refl

wl1034 : Base 4 → ⟪ (ℓ "乎亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么乎") ⟫ʷ
wl1034 c4 = lw0 c4 (ℓ "乎亭乇亭么") (ℓ "亭乇亭么乎") tt tt Eq.refl

wl1035 : Base 4 → ⟪ (ℓ "乏亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么乏") ⟫ʷ
wl1035 c4 = lw0 c4 (ℓ "乏亭乇亭么") (ℓ "亭乇亭么乏") tt tt Eq.refl

wl1036 : Base 4 → ⟪ (ℓ "交亰亭乇亰亭么並") ⟫ʷ ≈ ⟪ (ℓ "亰亭乇亰亭么並交") ⟫ʷ
wl1036 c4 = lw0 c4 (ℓ "交亰亭乇亰亭么並") (ℓ "亰亭乇亰亭么並交") tt tt Eq.refl

wl1037 : Base 4 → ⟪ (ℓ "亰亭乇") ⟫ʷ ≈ ⟪ (ℓ "亭乇亰") ⟫ʷ
wl1037 c4 = lw0 c4 (ℓ "亰亭乇") (ℓ "亭乇亰") tt tt Eq.refl

wl1038 : Base 4 → ⟪ (ℓ "乳亭亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么乳亭") ⟫ʷ
wl1038 c4 = lw0 c4 (ℓ "乳亭亭乇亭么") (ℓ "亭乇亭么乳亭") tt tt Eq.refl

wl1039 : Base 4 → ⟪ (ℓ "买乳云") ⟫ʷ ≈ ⟪ (ℓ "云乳") ⟫ʷ
wl1039 c4 = lw4 c4 (ℓ "买乳云") (ℓ "云乳") tt tt Eq.refl

wl1040 : Base 4 → ⟪ (ℓ "买云") ⟫ʷ ≈ ⟪ (ℓ "云买") ⟫ʷ
wl1040 c4 = lw4 c4 (ℓ "买云") (ℓ "云买") tt tt Eq.refl

wl1041 : Base 4 → ⟪ (ℓ "亰乳亰亭") ⟫ʷ ≈ ⟪ (ℓ "乳亭") ⟫ʷ
wl1041 c4 = lw0 c4 (ℓ "亰乳亰亭") (ℓ "乳亭") tt tt Eq.refl

wl1042 : Base 4 → ⟪ (ℓ "乇亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么乇") ⟫ʷ
wl1042 c4 = lw0 c4 (ℓ "乇亭乇亭么") (ℓ "亭乇亭么乇") tt tt Eq.refl

wl1043 : Base 4 → ⟪ (ℓ "么亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么么") ⟫ʷ
wl1043 c4 = lw0 c4 (ℓ "么亭乇亭么") (ℓ "亭乇亭么么") tt tt Eq.refl

wl1044 : Base 4 → ⟪ (ℓ "乕丢") ⟫ʷ ≈ ⟪ (ℓ "丢乕") ⟫ʷ
wl1044 c4 = lw0 c4 (ℓ "乕丢") (ℓ "丢乕") tt tt Eq.refl

wl1045 : Base 4 → ⟪ (ℓ "乩丢") ⟫ʷ ≈ ⟪ (ℓ "丢乩") ⟫ʷ
wl1045 c4 = lw0 c4 (ℓ "乩丢") (ℓ "丢乩") tt tt Eq.refl

wl1046 : Base 4 → ⟪ (ℓ "乹丢") ⟫ʷ ≈ ⟪ (ℓ "丢乹") ⟫ʷ
wl1046 c4 = lw0 c4 (ℓ "乹丢") (ℓ "丢乹") tt tt Eq.refl

wl1047 : Base 4 → ⟪ (ℓ "亄丢") ⟫ʷ ≈ ⟪ (ℓ "丢亄") ⟫ʷ
wl1047 c4 = lw0 c4 (ℓ "亄丢") (ℓ "丢亄") tt tt Eq.refl

wl1048 : Base 4 → ⟪ (ℓ "亇丢") ⟫ʷ ≈ ⟪ (ℓ "丢亇") ⟫ʷ
wl1048 c4 = lw0 c4 (ℓ "亇丢") (ℓ "丢亇") tt tt Eq.refl

wl1049 : Base 4 → ⟪ (ℓ "亊丢") ⟫ʷ ≈ ⟪ (ℓ "丢亊") ⟫ʷ
wl1049 c4 = lw0 c4 (ℓ "亊丢") (ℓ "丢亊") tt tt Eq.refl

wl1050 : Base 4 → ⟪ (ℓ "丢亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏丢") ⟫ʷ
wl1050 c4 = lw0 c4 (ℓ "丢亲乎亲乏") (ℓ "亲乎亲乏丢") tt tt Eq.refl

wl1051 : Base 4 → ⟪ (ℓ "丢亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么丢") ⟫ʷ
wl1051 c4 = lw0 c4 (ℓ "丢亭乇亭么") (ℓ "亭乇亭么丢") tt tt Eq.refl

wl1052 : Base 4 → ⟪ (ℓ "乕乩") ⟫ʷ ≈ ⟪ (ℓ "乩乕") ⟫ʷ
wl1052 c4 = lw0 c4 (ℓ "乕乩") (ℓ "乩乕") tt tt Eq.refl

wl1053 : Base 4 → ⟪ (ℓ "乕乹") ⟫ʷ ≈ ⟪ (ℓ "乹乕") ⟫ʷ
wl1053 c4 = lw0 c4 (ℓ "乕乹") (ℓ "乹乕") tt tt Eq.refl

wl1054 : Base 4 → ⟪ (ℓ "亇乕") ⟫ʷ ≈ ⟪ (ℓ "乕亇") ⟫ʷ
wl1054 c4 = lw0 c4 (ℓ "亇乕") (ℓ "乕亇") tt tt Eq.refl

wl1055 : Base 4 → ⟪ (ℓ "亊乕") ⟫ʷ ≈ ⟪ (ℓ "乕亊") ⟫ʷ
wl1055 c4 = lw0 c4 (ℓ "亊乕") (ℓ "乕亊") tt tt Eq.refl

wl1056 : Base 4 → ⟪ (ℓ "乕亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么乕") ⟫ʷ
wl1056 c4 = lw0 c4 (ℓ "乕亭乇亭么") (ℓ "亭乇亭么乕") tt tt Eq.refl

wl1057 : Base 4 → ⟪ (ℓ "乩乹") ⟫ʷ ≈ ⟪ (ℓ "乹乩") ⟫ʷ
wl1057 c4 = lw0 c4 (ℓ "乩乹") (ℓ "乹乩") tt tt Eq.refl

wl1058 : Base 4 → ⟪ (ℓ "亄乩") ⟫ʷ ≈ ⟪ (ℓ "乩亄") ⟫ʷ
wl1058 c4 = lw0 c4 (ℓ "亄乩") (ℓ "乩亄") tt tt Eq.refl

wl1059 : Base 4 → ⟪ (ℓ "亊乩") ⟫ʷ ≈ ⟪ (ℓ "乩亊") ⟫ʷ
wl1059 c4 = lw0 c4 (ℓ "亊乩") (ℓ "乩亊") tt tt Eq.refl

wl1060 : Base 4 → ⟪ (ℓ "亄乹") ⟫ʷ ≈ ⟪ (ℓ "乹亄") ⟫ʷ
wl1060 c4 = lw0 c4 (ℓ "亄乹") (ℓ "乹亄") tt tt Eq.refl

wl1061 : Base 4 → ⟪ (ℓ "亇乹") ⟫ʷ ≈ ⟪ (ℓ "乹亇") ⟫ʷ
wl1061 c4 = lw0 c4 (ℓ "亇乹") (ℓ "乹亇") tt tt Eq.refl

wl1062 : Base 4 → ⟪ (ℓ "乹亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏乹") ⟫ʷ
wl1062 c4 = lw0 c4 (ℓ "乹亲乎亲乏") (ℓ "亲乎亲乏乹") tt tt Eq.refl

wl1063 : Base 4 → ⟪ (ℓ "亄亇") ⟫ʷ ≈ ⟪ (ℓ "亇亄") ⟫ʷ
wl1063 c4 = lw0 c4 (ℓ "亄亇") (ℓ "亇亄") tt tt Eq.refl

wl1064 : Base 4 → ⟪ (ℓ "亄亊") ⟫ʷ ≈ ⟪ (ℓ "亊亄") ⟫ʷ
wl1064 c4 = lw0 c4 (ℓ "亄亊") (ℓ "亊亄") tt tt Eq.refl

wl1065 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "个交个") ⟫ʷ
wl1065 c4 = lw4 c4 (ℓ "交") (ℓ "个交个") tt tt Eq.refl

wl1066 : Base 4 → ⟪ (ℓ "交亄交亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么亄") ⟫ʷ
wl1066 c4 = lw0 c4 (ℓ "交亄交亭乇亭么") (ℓ "亭乇亭么亄") tt tt Eq.refl

wl1067 : Base 4 → ⟪ (ℓ "亇亊") ⟫ʷ ≈ ⟪ (ℓ "亊亇") ⟫ʷ
wl1067 c4 = lw0 c4 (ℓ "亇亊") (ℓ "亊亇") tt tt Eq.refl

wl1068 : Base 4 → ⟪ (ℓ "亇亮") ⟫ʷ ≈ ⟪ (ℓ "亮亇") ⟫ʷ
wl1068 c4 = lw0 c4 (ℓ "亇亮") (ℓ "亮亇") tt tt Eq.refl

wl1069 : Base 4 → ⟪ (ℓ "亰乤亊乤") ⟫ʷ ≈ ⟪ (ℓ "亊亰") ⟫ʷ
wl1069 c4 = lw0 c4 (ℓ "亰乤亊乤") (ℓ "亊亰") tt tt Eq.refl

wl1070 : Base 4 → ⟪ (ℓ "乤亏") ⟫ʷ ≈ ⟪ (ℓ "亏乤亐") ⟫ʷ
wl1070 c4 = lw4 c4 (ℓ "乤亏") (ℓ "亏乤亐") tt tt Eq.refl

wl1071 : Base 4 → ⟪ (ℓ "亰乤") ⟫ʷ ≈ ⟪ (ℓ "乤亰") ⟫ʷ
wl1071 c4 = lw0 c4 (ℓ "亰乤") (ℓ "乤亰") tt tt Eq.refl

wl1072 : Base 4 → ⟪ (ℓ "乤亊乤乤") ⟫ʷ ≈ ⟪ (ℓ "乤亊") ⟫ʷ
wl1072 c4 = lw0 c4 (ℓ "乤亊乤乤") (ℓ "乤亊") tt tt Eq.refl

wl1073 : Base 4 → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "乤亐乤") ⟫ʷ
wl1073 c4 = lw4 c4 (ℓ "亐") (ℓ "乤亐乤") tt tt Eq.refl

wl1074 : Base 4 → ⟪ (ℓ "丸亍") ⟫ʷ ≈ ⟪ (ℓ "亍丸交") ⟫ʷ
wl1074 c4 = lw4 c4 (ℓ "丸亍") (ℓ "亍丸交") tt tt Eq.refl

wl1075 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "丸交丸") ⟫ʷ
wl1075 c4 = lw4 c4 (ℓ "交") (ℓ "丸交丸") tt tt Eq.refl

wl1076 : Base 4 → ⟪ (ℓ "交亊交亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏亊") ⟫ʷ
wl1076 c4 = lw0 c4 (ℓ "交亊交亲乎亲乏") (ℓ "亲乎亲乏亊") tt tt Eq.refl

wl1077 : Base 4 → ⟪ (ℓ "丷丶") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1077 c4 = lw4 c4 (ℓ "丷丶") [] tt tt Eq.refl

wl1078 : Base 4 → ⟪ (ℓ "丶丷") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1078 c4 = lw4 c4 (ℓ "丶丷") [] tt tt Eq.refl

wl1079 : Base 4 → ⟪ (ℓ "二亍丸亍二丸丸二亍丸亍二") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1079 c4 = lw4 c4 (ℓ "二亍丸亍二丸丸二亍丸亍二") [] tt tt Eq.refl

wl1080 : Base 4 → ⟪ (ℓ "丸二亍丸亍二二亍丸亍二丸") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1080 c4 = lw4 c4 (ℓ "丸二亍丸亍二二亍丸亍二丸") [] tt tt Eq.refl

wl1081 : Base 4 → ⟪ (ℓ "丨云") ⟫ʷ ≈ ⟪ (ℓ "云丨乎亐") ⟫ʷ
wl1081 c4 = lw4 c4 (ℓ "丨云") (ℓ "云丨乎亐") tt tt Eq.refl

wl1082 : Base 4 → ⟪ (ℓ "丨乎亐乎乐亐") ⟫ʷ ≈ ⟪ (ℓ "丨") ⟫ʷ
wl1082 c4 = lw4 c4 (ℓ "丨乎亐乎乐亐") (ℓ "丨") tt tt Eq.refl

wl1083 : Base 4 → ⟪ (ℓ "並並") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1083 c4 = lw0 c4 (ℓ "並並") [] tt tt Eq.refl

wl1084 : Base 4 → ⟪ (ℓ "亍产亓") ⟫ʷ ≈ ⟪ (ℓ "亓亍") ⟫ʷ
wl1084 c4 = lw4 c4 (ℓ "亍产亓") (ℓ "亓亍") tt tt Eq.refl

wl1085 : Base 4 → ⟪ (ℓ "亍产") ⟫ʷ ≈ ⟪ (ℓ "产亍") ⟫ʷ
wl1085 c4 = lw4 c4 (ℓ "亍产") (ℓ "产亍") tt tt Eq.refl

wl1086 : Base 4 → ⟪ (ℓ "亐丠个") ⟫ʷ ≈ ⟪ (ℓ "丠亐") ⟫ʷ
wl1086 c4 = lw4 c4 (ℓ "亐丠个") (ℓ "丠亐") tt tt Eq.refl

wl1087 : Base 4 → ⟪ (ℓ "亐个") ⟫ʷ ≈ ⟪ (ℓ "个亐") ⟫ʷ
wl1087 c4 = lw4 c4 (ℓ "亐个") (ℓ "个亐") tt tt Eq.refl

wl1088 : Base 4 → ⟪ (ℓ "丠个个") ⟫ʷ ≈ ⟪ (ℓ "丠") ⟫ʷ
wl1088 c4 = lw4 c4 (ℓ "丠个个") (ℓ "丠") tt tt Eq.refl

wl1089 : Base 4 → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "丠亨丠") ⟫ʷ
wl1089 c4 = lw0 c4 (ℓ "亨") (ℓ "丠亨丠") tt tt Eq.refl

wl1090 : Base 4 → ⟪ (ℓ "亨乾亨亨") ⟫ʷ ≈ ⟪ (ℓ "亨乾") ⟫ʷ
wl1090 c4 = lw0 c4 (ℓ "亨乾亨亨") (ℓ "亨乾") tt tt Eq.refl

wl1091 : Base 4 → ⟪ (ℓ "亨丠") ⟫ʷ ≈ ⟪ (ℓ "丠亨") ⟫ʷ
wl1091 c4 = lw0 c4 (ℓ "亨丠") (ℓ "丠亨") tt tt Eq.refl

wl1092 : Base 4 → ⟪ (ℓ "两乾东丠") ⟫ʷ ≈ ⟪ (ℓ "丠乾") ⟫ʷ
wl1092 c4 = lw0 c4 (ℓ "两乾东丠") (ℓ "丠乾") tt tt Eq.refl

wl1093 : Base 4 → ⟪ (ℓ "亨乾亨丠") ⟫ʷ ≈ ⟪ (ℓ "丠亨两乾东亨") ⟫ʷ
wl1093 c4 = lw0 c4 (ℓ "亨乾亨丠") (ℓ "丠亨两乾东亨") tt tt Eq.refl

wl1094 : Base 4 → ⟪ (ℓ "亨乿亨亨") ⟫ʷ ≈ ⟪ (ℓ "亨乿") ⟫ʷ
wl1094 c4 = lw0 c4 (ℓ "亨乿亨亨") (ℓ "亨乿") tt tt Eq.refl

wl1095 : Base 4 → ⟪ (ℓ "两乾一丠") ⟫ʷ ≈ ⟪ (ℓ "丠乿") ⟫ʷ
wl1095 c4 = lw1 c4 (ℓ "两乾一丠") (ℓ "丠乿") tt tt Eq.refl

wl1096 : Base 4 → ⟪ (ℓ "亨乾东亨") ⟫ʷ ≈ ⟪ (ℓ "亨乿亨") ⟫ʷ
wl1096 c4 = lw0 c4 (ℓ "亨乾东亨") (ℓ "亨乿亨") tt tt Eq.refl

wl1097 : Base 4 → ⟪ (ℓ "亰之京") ⟫ʷ ≈ ⟪ (ℓ "之亰") ⟫ʷ
wl1097 c4 = lw0 c4 (ℓ "亰之京") (ℓ "之亰") tt tt Eq.refl

wl1098 : Base 4 → ⟪ (ℓ "之京京") ⟫ʷ ≈ ⟪ (ℓ "之") ⟫ʷ
wl1098 c4 = lw0 c4 (ℓ "之京京") (ℓ "之") tt tt Eq.refl

wl1099 : Base 4 → ⟪ (ℓ "也亓") ⟫ʷ ≈ ⟪ (ℓ "亓也些") ⟫ʷ
wl1099 c4 = lw4 c4 (ℓ "也亓") (ℓ "亓也些") tt tt Eq.refl

wl1100 : Base 4 → ⟪ (ℓ "亓些") ⟫ʷ ≈ ⟪ (ℓ "些亓") ⟫ʷ
wl1100 c4 = lw4 c4 (ℓ "亓些") (ℓ "些亓") tt tt Eq.refl

wl1101 : Base 4 → ⟪ (ℓ "也些些") ⟫ʷ ≈ ⟪ (ℓ "也") ⟫ʷ
wl1101 c4 = lw4 c4 (ℓ "也些些") (ℓ "也") tt tt Eq.refl

wl1102 : Base 4 → ⟪ (ℓ "丢丢丢丢") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1102 c4 = lw0 c4 (ℓ "丢丢丢丢") [] tt tt Eq.refl

wl1103 : Base 4 → ⟪ (ℓ "乕乕乕乕") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1103 c4 = lw0 c4 (ℓ "乕乕乕乕") [] tt tt Eq.refl

wl1104 : Base 4 → ⟪ (ℓ "乩乩乩乩") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1104 c4 = lw0 c4 (ℓ "乩乩乩乩") [] tt tt Eq.refl

wl1105 : Base 4 → ⟪ (ℓ "乹乹乹乹") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1105 c4 = lw0 c4 (ℓ "乹乹乹乹") [] tt tt Eq.refl

wl1106 : Base 4 → ⟪ (ℓ "亄亄") ⟫ʷ ≈ ⟪ (ℓ "丢丢丢") ⟫ʷ
wl1106 c4 = lw0 c4 (ℓ "亄亄") (ℓ "丢丢丢") tt tt Eq.refl

wl1107 : Base 4 → ⟪ (ℓ "亇亇") ⟫ʷ ≈ ⟪ (ℓ "丢丢丢") ⟫ʷ
wl1107 c4 = lw0 c4 (ℓ "亇亇") (ℓ "丢丢丢") tt tt Eq.refl

wl1108 : Base 4 → ⟪ (ℓ "亊亊") ⟫ʷ ≈ ⟪ (ℓ "丢丢丢") ⟫ʷ
wl1108 c4 = lw0 c4 (ℓ "亊亊") (ℓ "丢丢丢") tt tt Eq.refl

wl1109 : Base 4 → ⟪ (ℓ "乕亄乕亄乕亄") ⟫ʷ ≈ ⟪ (ℓ "丢丢丢") ⟫ʷ
wl1109 c4 = lw0 c4 (ℓ "乕亄乕亄乕亄") (ℓ "丢丢丢") tt tt Eq.refl

wl1110 : Base 4 → ⟪ (ℓ "乩亇乩亇乩亇") ⟫ʷ ≈ ⟪ (ℓ "丢丢丢") ⟫ʷ
wl1110 c4 = lw0 c4 (ℓ "乩亇乩亇乩亇") (ℓ "丢丢丢") tt tt Eq.refl

wl1111 : Base 4 → ⟪ (ℓ "乹亊乹亊乹亊") ⟫ʷ ≈ ⟪ (ℓ "丢丢丢") ⟫ʷ
wl1111 c4 = lw0 c4 (ℓ "乹亊乹亊乹亊") (ℓ "丢丢丢") tt tt Eq.refl

wl1112 : Base 4 → ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1112 c4 = lw4 c4 [] [] tt tt Eq.refl

wl1113 : Base 4 → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏亲乎亲乏") ⟫ʷ
wl1113 c4 = lw0 c4 (ℓ "亨") (ℓ "亲乎亲乏亲乎亲乏") tt tt Eq.refl

wl1114 : Base 4 → ⟪ (ℓ "亰") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么亭乇亭么") ⟫ʷ
wl1114 c4 = lw0 c4 (ℓ "亰") (ℓ "亭乇亭么亭乇亭么") tt tt Eq.refl

wl1115 : Base 4 → ⟪ (ℓ "乕亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏乕") ⟫ʷ
wl1115 c4 = lw0 c4 (ℓ "乕亲乎亲乏") (ℓ "亲乎亲乏乕") tt tt Eq.refl

wl1116 : Base 4 → ⟪ (ℓ "乩亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么乩") ⟫ʷ
wl1116 c4 = lw0 c4 (ℓ "乩亭乇亭么") (ℓ "亭乇亭么乩") tt tt Eq.refl

wl1117 : Base 4 → ⟪ (ℓ "乩亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏乩") ⟫ʷ
wl1117 c4 = lw0 c4 (ℓ "乩亲乎亲乏") (ℓ "亲乎亲乏乩") tt tt Eq.refl

wl1118 : Base 4 → ⟪ (ℓ "乹亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么乹") ⟫ʷ
wl1118 c4 = lw0 c4 (ℓ "乹亭乇亭么") (ℓ "亭乇亭么乹") tt tt Eq.refl

wl1119 : Base 4 → ⟪ (ℓ "亘亦") ⟫ʷ ≈ ⟪ (ℓ "亦亘亐") ⟫ʷ
wl1119 c4 = lw4 c4 (ℓ "亘亦") (ℓ "亦亘亐") tt tt Eq.refl

wl1120 : Base 4 → ⟪ (ℓ "争亦") ⟫ʷ ≈ ⟪ (ℓ "亦争亪") ⟫ʷ
wl1120 c4 = lw0 c4 (ℓ "争亦") (ℓ "亦争亪") tt tt Eq.refl

wl1121 : Base 4 → ⟪ (ℓ "争亪亪") ⟫ʷ ≈ ⟪ (ℓ "争") ⟫ʷ
wl1121 c4 = lw0 c4 (ℓ "争亪亪") (ℓ "争") tt tt Eq.refl

wl1122 : Base 4 → ⟪ (ℓ "亨乼") ⟫ʷ ≈ ⟪ (ℓ "乼交") ⟫ʷ
wl1122 c4 = lw0 c4 (ℓ "亨乼") (ℓ "乼交") tt tt Eq.refl

wl1123 : Base 4 → ⟪ (ℓ "乼亦") ⟫ʷ ≈ ⟪ (ℓ "亪乼") ⟫ʷ
wl1123 c4 = lw0 c4 (ℓ "乼亦") (ℓ "亪乼") tt tt Eq.refl

wl1124 : Base 4 → ⟪ (ℓ "交乼") ⟫ʷ ≈ ⟪ (ℓ "乼亨") ⟫ʷ
wl1124 c4 = lw0 c4 (ℓ "交乼") (ℓ "乼亨") tt tt Eq.refl

wl1125 : Base 4 → ⟪ (ℓ "乼亩") ⟫ʷ ≈ ⟪ (ℓ "亥乼") ⟫ʷ
wl1125 c4 = lw0 c4 (ℓ "乼亩") (ℓ "亥乼") tt tt Eq.refl

wl1126 : Base 4 → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "交亥个亥交个") ⟫ʷ
wl1126 c4 = lw4 c4 (ℓ "亘") (ℓ "交亥个亥交个") tt tt Eq.refl

wl1127 : Base 4 → ⟪ (ℓ "亨並义") ⟫ʷ ≈ ⟪ (ℓ "並亨") ⟫ʷ
wl1127 c4 = lw0 c4 (ℓ "亨並义") (ℓ "並亨") tt tt Eq.refl

wl1128 : Base 4 → ⟪ (ℓ "义亚") ⟫ʷ ≈ ⟪ (ℓ "亚义亐") ⟫ʷ
wl1128 c4 = lw4 c4 (ℓ "义亚") (ℓ "亚义亐") tt tt Eq.refl

wl1129 : Base 4 → ⟪ (ℓ "亨义") ⟫ʷ ≈ ⟪ (ℓ "义亨") ⟫ʷ
wl1129 c4 = lw0 c4 (ℓ "亨义") (ℓ "义亨") tt tt Eq.refl

wl1130 : Base 4 → ⟪ (ℓ "並义义") ⟫ʷ ≈ ⟪ (ℓ "並") ⟫ʷ
wl1130 c4 = lw0 c4 (ℓ "並义义") (ℓ "並") tt tt Eq.refl

wl1131 : Base 4 → ⟪ (ℓ "亐亚") ⟫ʷ ≈ ⟪ (ℓ "亚亐") ⟫ʷ
wl1131 c4 = lw4 c4 (ℓ "亐亚") (ℓ "亚亐") tt tt Eq.refl

wl1132 : Base 4 → ⟪ (ℓ "争亪") ⟫ʷ ≈ ⟪ (ℓ "亪争") ⟫ʷ
wl1132 c4 = lw0 c4 (ℓ "争亪") (ℓ "亪争") tt tt Eq.refl

wl1133 : Base 4 → ⟪ (ℓ "乽亪") ⟫ʷ ≈ ⟪ (ℓ "亪乽亦") ⟫ʷ
wl1133 c4 = lw0 c4 (ℓ "乽亪") (ℓ "亪乽亦") tt tt Eq.refl

wl1134 : Base 4 → ⟪ (ℓ "亘亦亐") ⟫ʷ ≈ ⟪ (ℓ "亦亘") ⟫ʷ
wl1134 c4 = lw4 c4 (ℓ "亘亦亐") (ℓ "亦亘") tt tt Eq.refl

wl1135 : Base 4 → ⟪ (ℓ "乒亪") ⟫ʷ ≈ ⟪ (ℓ "亪乒") ⟫ʷ
wl1135 c4 = lw0 c4 (ℓ "乒亪") (ℓ "亪乒") tt tt Eq.refl

wl1136 : Base 4 → ⟪ (ℓ "乽亦亦") ⟫ʷ ≈ ⟪ (ℓ "乽") ⟫ʷ
wl1136 c4 = lw0 c4 (ℓ "乽亦亦") (ℓ "乽") tt tt Eq.refl

wl1137 : Base 4 → ⟪ (ℓ "乼亪") ⟫ʷ ≈ ⟪ (ℓ "亦乼") ⟫ʷ
wl1137 c4 = lw0 c4 (ℓ "乼亪") (ℓ "亦乼") tt tt Eq.refl

wl1138 : Base 4 → ⟪ (ℓ "乼亥") ⟫ʷ ≈ ⟪ (ℓ "亩乼") ⟫ʷ
wl1138 c4 = lw0 c4 (ℓ "乼亥") (ℓ "亩乼") tt tt Eq.refl

wl1139 : Base 4 → ⟪ (ℓ "交亄交交") ⟫ʷ ≈ ⟪ (ℓ "交亄") ⟫ʷ
wl1139 c4 = lw0 c4 (ℓ "交亄交交") (ℓ "交亄") tt tt Eq.refl
