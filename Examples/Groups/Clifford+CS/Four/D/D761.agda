{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD761 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D761 (W : Ws) (Sᴰ : SD761) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK20-X2 : St 1223
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK20-X2 = pickᴰ 0 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd20-X2 : St 1224
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd20-X2 = pickᴰ 1 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK20-X2 : St 1249
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK20-X2 = pickᴰ 2 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd20-X2 : St 1250
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd20-X2 = pickᴰ 3 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS02-X2 : St 2783
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS02-X2 = pickᴰ 4 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd02-X2 : St 2784
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd02-X2 = pickᴰ 5 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS02-X2 : St 2785
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS02-X2 = pickᴰ 6 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd02-X2 : St 2786
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd02-X2 = pickᴰ 7 Sᴰ
  lem-b2g-0011PP2 : St 2940
  lem-b2g-0011PP2 = pickᴰ 8 Sᴰ
  lem-AXIOM-LF-at0321 : St 1002
  lem-AXIOM-LF-at0321 = pickᴰ 9 Sᴰ
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ : St 2941
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ = pickᴰ 10 Sᴰ
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ : St 2942
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ = pickᴰ 11 Sᴰ
  lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 1765
  lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 12 Sᴰ
  lem-pass-CS20-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 2943
  lem-pass-CS20-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 13 Sᴰ
  lem-pass-CSd20-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 2944
  lem-pass-CSd20-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 14 Sᴰ
  lem-Bar⟨SSSKSS13-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩ : St 2945
  lem-Bar⟨SSSKSS13-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩ = pickᴰ 15 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ : St 2946
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ = pickᴰ 16 Sᴰ
  lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩ : St 2947
  lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩ = pickᴰ 17 Sᴰ
  lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ : St 2948
  lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ = pickᴰ 18 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ : St 2949
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ = pickᴰ 19 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ : St 2950
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ = pickᴰ 20 Sᴰ
  lem-CCZ⟨231⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : St 2951
  lem-CCZ⟨231⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 21 Sᴰ
  lem-CCZ⟨312⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩ : St 2952
  lem-CCZ⟨312⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩ = pickᴰ 22 Sᴰ
  lem-pass-CS30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 2953
  lem-pass-CS30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 23 Sᴰ
  lem-pass-CSd30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 2954
  lem-pass-CSd30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 24 Sᴰ
  lem-CCZ⟨321⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ : St 2955
  lem-CCZ⟨321⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 25 Sᴰ
  lem-pass-CSd20-vs-X2-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2-X3 : St 2956
  lem-pass-CSd20-vs-X2-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2-X3 = pickᴰ 26 Sᴰ
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩ : St 2957
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩ = pickᴰ 27 Sᴰ
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ : St 2958
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 28 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩ : St 2959
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩ = pickᴰ 29 Sᴰ
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩ : St 2960
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩ = pickᴰ 30 Sᴰ
  lem-CA-CKd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡-1⟩ : St 2961
  lem-CA-CKd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡-1⟩ = pickᴰ 31 Sᴰ
  lem-pass-CK10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 2760
  lem-pass-CK10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 32 Sᴰ
  lem-pass-CK31-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : St 2962
  lem-pass-CK31-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = pickᴰ 33 Sᴰ
  lem-pass-CKd31-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : St 2963
  lem-pass-CKd31-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = pickᴰ 34 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ : St 2964
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 35 Sᴰ
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ : St 2965
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 36 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 : St 2966
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 = pickᴰ 37 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 : St 2967
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 = pickᴰ 38 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 : St 2968
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 = pickᴰ 39 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩-1 : St 2969
  lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩-1 = pickᴰ 40 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2 : St 2970
  lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2 = pickᴰ 41 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩-3 : St 2971
  lem-ca-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩-3 = pickᴰ 42 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2 : St 2929
  lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2 = pickᴰ 43 Sᴰ
  lem-ca-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩-3 : St 2972
  lem-ca-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩-3 = pickᴰ 44 Sᴰ
  lem-pass-CCZ123-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : St 2973
  lem-pass-CCZ123-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = pickᴰ 45 Sᴰ
  lem-pass-CKd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 2931
  lem-pass-CKd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 46 Sᴰ
  lem-CA-CK10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Kd-e≡-1⟩ : St 2974
  lem-CA-CK10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Kd-e≡-1⟩ = pickᴰ 47 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩-2 : St 2975
  lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩-2 = pickᴰ 48 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2976
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 49 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2977
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 50 Sᴰ
  lem-pass-TOFF123-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 : St 2978
  lem-pass-TOFF123-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 = pickᴰ 51 Sᴰ

private
  q1 : Eqn
  q1 = sE 2929 lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2
  q2 : Eqn
  q2 = sE 2946 lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩
  q3 : Eqn
  q3 = sE 2929 lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丞与丐丽习举习丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐丽习举习丑丏丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丞与丐丽习举习丑丏丘丞") (ℓ "丘丞与丐丽习举习丑丏丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 31 q1 ∷
   rw 0 q2 ∷
   rw⁻ 0 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = sE 2942 lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丞与丐丽习举习丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐丽习举习丑丏丘丞丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丞与丐丽习举习丑丏丘丞") (ℓ "丘丞与丐丽习举习丑丏丘丞丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 29 q1 ∷
   rw 0 q4 ∷
   rw⁻ 0 q3 ∷ []) Eq.refl

private
  q5 : Eqn
  q5 = wE 2502 W
  q6 : Eqn
  q6 = sE 2963 lem-pass-CKd31-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3
  q7 : Eqn
  q7 = sE 2973 lem-pass-CCZ123-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3
  q8 : Eqn
  q8 = sE 2962 lem-pass-CK31-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3
  q9 : Eqn
  q9 = wE 2503 W

-- pass [TOFF123] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 5 steps
lem-pass-TOFF123-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (ℓ "乢丞丕丗且且义乣乊乣丕丕世且丞") ⟫ʷ ≈ ⟪ (ℓ "丞丕丗且且义乣乊乣丕丕世且丞乢") ⟫ʷ
lem-pass-TOFF123-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = derive (ℓ "乢丞丕丗且且义乣乊乣丕丕世且丞") (ℓ "丞丕丗且且义乣乊乣丕丕世且丞乢")
  (rw 0 q5 ∷
   rw 2 q6 ∷
   rw 1 q7 ∷
   rw 0 q8 ∷
   rw 14 q9 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = wE 1 W
  q11 : Eqn
  q11 = wE 3 W
  q12 : Eqn
  q12 = wE 464 W
  q13 : Eqn
  q13 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q14 : Eqn
  q14 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q15 : Eqn
  q15 = wE 1416 W
  q16 : Eqn
  q16 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q17 : Eqn
  q17 = sE 2954 lem-pass-CSd30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q18 : Eqn
  q18 = sE 2931 lem-pass-CKd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q19 : Eqn
  q19 = sE 2953 lem-pass-CS30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q20 : Eqn
  q20 = sE 2760 lem-pass-CK10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q21 : Eqn
  q21 = wE 1417 W
  q22 : Eqn
  q22 = wE 151 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 120 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒丘丞中九丮九丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞中九丮九丒丘丞丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒丘丞中九丮九丒丘丞") (ℓ "丒丘丞中九丮九丒丘丞丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 29 q10 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q11 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q11 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q11 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw 27 q11 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q11 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q11 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 24 q11 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q11 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q11 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q11 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q11 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q11 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q11 ∷
   rw 15 q12 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q11 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q11 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q11 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q11 ∷
   rw 10 q12 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q11 ∷
   rw 8 q12 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q11 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q11 ∷
   rw 5 q13 ∷
   rw 4 q13 ∷
   rw 3 q14 ∷
   rw 2 q13 ∷
   rw 1 q14 ∷
   rw 0 q14 ∷
   rw 1 q15 ∷
   rw⁻ 0 q13 ∷
   rw 3 q10 ∷
   re 1 3 (ℓ "中") ∷
   rw⁻ 2 q16 ∷
   rw 5 q10 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q11 ∷
   rw 3 q17 ∷
   rw 2 q18 ∷
   rw 1 q19 ∷
   rw 0 q20 ∷
   rw 14 q10 ∷
   re 13 1 (ℓ "乏丨乏") ∷
   rw 15 q11 ∷
   rw 12 q16 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q11 ∷
   rw 10 q13 ∷
   rw 11 q21 ∷
   rw⁻ 10 q14 ∷
   rw⁻ 11 q14 ∷
   rw⁻ 12 q13 ∷
   rw⁻ 13 q14 ∷
   rw⁻ 14 q13 ∷
   rw⁻ 15 q13 ∷
   rw 18 q10 ∷
   re 16 3 (ℓ "乀") ∷
   rw 19 q10 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q22 ∷
   rw 21 q10 ∷
   re 19 3 (ℓ "乑") ∷
   rw 20 q22 ∷
   rw 23 q10 ∷
   re 21 3 (ℓ "中") ∷
   rw 24 q10 ∷
   re 22 3 (ℓ "中") ∷
   rw 25 q10 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q10 ∷
   re 24 3 (ℓ "乑") ∷
   rw 25 q22 ∷
   rw 28 q10 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q10 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q10 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q10 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q10 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q10 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q10 ∷
   re 32 3 (ℓ "乀") ∷
   rw 35 q10 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q10 ∷
   re 34 3 (ℓ "中") ∷
   rw 37 q10 ∷
   re 35 3 (ℓ "乑") ∷
   rw 38 q10 ∷
   re 36 3 (ℓ "中") ∷
   rw 39 q10 ∷
   re 37 3 (ℓ "乑") ∷
   rw 40 q10 ∷
   re 38 3 (ℓ "乑") ∷
   rw 39 q11 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = sE 2969 lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩-1
  q24 : Eqn
  q24 = sE 2947 lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩
  q25 : Eqn
  q25 = sE 2969 lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩-1

-- pass [CCZ123] [X1 X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X1 X2 X3]: 3 steps
lem-pass-CCZ123-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 : ⟪ (ℓ "乜丒丘丞丈上中九丮九下三丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞丈上中九丮九下三丒丘丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 = derive (ℓ "乜丒丘丞丈上中九丮九下三丒丘丞") (ℓ "丒丘丞丈上中九丮九下三丒丘丞乜")
  (rw 1 q23 ∷
   rw 0 q24 ∷
   rw⁻ 0 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = sE 2945 lem-Bar⟨SSSKSS13-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [X1 X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X1 X2 X3]: 3 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒丘丞丈上中九丮九下三丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞丈上中九丮九下三丒丘丞丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒丘丞丈上中九丮九下三丒丘丞") (ℓ "丒丘丞丈上中九丮九下三丒丘丞丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (rw 31 q23 ∷
   rw 0 q26 ∷
   rw⁻ 0 q25 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = sE 2944 lem-pass-CSd20-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q28 : Eqn
  q28 = sE 2943 lem-pass-CS20-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 6 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒丘丞中九丮九丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞中九丮九丒丘丞丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = derive (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒丘丞中九丮九丒丘丞") (ℓ "丒丘丞中九丮九丒丘丞丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄")
  (rw 0 q15 ∷
   rw 3 q27 ∷
   rw 2 q18 ∷
   rw 1 q28 ∷
   rw 0 q20 ∷
   rw 10 q21 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = sE 2971 lem-ca-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩-3
  q30 : Eqn
  q30 = sE 2959 lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩
  q31 : Eqn
  q31 = sE 2971 lem-ca-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩-3

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X0 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X0 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丞与丐丽习举习丑丏丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞与丐丽习举习丑丏丌丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丞与丐丽习举习丑丏丌丞") (ℓ "丌丞与丐丽习举习丑丏丌丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 29 q29 ∷
   rw 0 q30 ∷
   rw⁻ 0 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = sE 2952 lem-CCZ⟨312⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩

-- pass [CCZ123] [X0 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X0 X3]: 3 steps
lem-pass-CCZ123-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 : ⟪ (ℓ "乜丌丞与丐丽习举习丑丏丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞与丐丽习举习丑丏丌丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 = derive (ℓ "乜丌丞与丐丽习举习丑丏丌丞") (ℓ "丌丞与丐丽习举习丑丏丌丞乜")
  (rw 1 q29 ∷
   rw 0 q32 ∷
   rw⁻ 0 q31 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = sE 2960 lem-Bar⟨SSSKSS32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X0 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X0 X3]: 3 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丌丞与丐丽习举习丑丏丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞与丐丽习举习丑丏丌丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丌丞与丐丽习举习丑丏丌丞") (ℓ "丌丞与丐丽习举习丑丏丌丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 31 q29 ∷
   rw 0 q33 ∷
   rw⁻ 0 q31 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = sE 2957 lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X0 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X0 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞与丐丽习举习丑丏丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞与丐丽习举习丑丏丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞与丐丽习举习丑丏丌丞") (ℓ "丌丞与丐丽习举习丑丏丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 29 q29 ∷
   rw 0 q34 ∷
   rw⁻ 0 q31 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = sE 2784 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd02-X2
  q36 : Eqn
  q36 = sE 1224 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd20-X2
  q37 : Eqn
  q37 = sE 2783 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS02-X2
  q38 : Eqn
  q38 = sE 2976 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q39 : Eqn
  q39 = sE 1223 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK20-X2

-- Bar(SSKSKK;2,1->0) passes split Gad(t=0, W=(2, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丨丘丘久丘丘丧丘丘丧丘丘丞中九丮九丘丞丘丨丘丘丨丘丘乄丘丘丧丘") ⟫ʷ ≈ ⟪ (ℓ "丘丨丘丘久丘丘丧丘丘丧丘丘丞中九丮九丘丞丘丨丘丘丨丘丘乄丘丘丧丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丨丘丘久丘丘丧丘丘丧丘丘丞中九丮九丘丞丘丨丘丘丨丘丘乄丘丘丧丘") (ℓ "丘丨丘丘久丘丘丧丘丘丧丘丘丞中九丮九丘丞丘丨丘丘丨丘丘乄丘丘丧丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q35 ∷
   rw 3 q36 ∷
   rw 6 q37 ∷
   rw 9 q37 ∷
   rw 12 q38 ∷
   rw 20 q35 ∷
   rw 23 q35 ∷
   rw 26 q39 ∷
   rw 29 q37 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = sE 2970 lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2
  q41 : Eqn
  q41 = sE 2951 lem-CCZ⟨231⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩
  q42 : Eqn
  q42 = sE 2970 lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2

-- pass [CCZ123] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 3 steps
lem-pass-CCZ123-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (ℓ "乜丘丞三下丈丈中九丮九三三上丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = derive (ℓ "乜丘丞三下丈丈中九丮九三三上丈丘丞") (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞乜")
  (rw 1 q40 ∷
   rw 0 q41 ∷
   rw⁻ 0 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = wE 2507 W
  q44 : Eqn
  q44 = sE 2961 lem-CA-CKd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡-1⟩
  q45 : Eqn
  q45 = sE 2956 lem-pass-CSd20-vs-X2-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2-X3
  q46 : Eqn
  q46 = sE 2974 lem-CA-CK10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Kd-e≡-1⟩
  q47 : Eqn
  q47 = sE 1765 lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q48 : Eqn
  q48 = wE 2508 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 6 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q43 ∷
   rw 3 q44 ∷
   rw 2 q45 ∷
   rw 1 q46 ∷
   rw 0 q47 ∷
   rw 8 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = sE 2786 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd02-X2
  q50 : Eqn
  q50 = sE 1250 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd20-X2
  q51 : Eqn
  q51 = sE 2785 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS02-X2
  q52 : Eqn
  q52 = sE 2977 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q53 : Eqn
  q53 = sE 1249 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK20-X2

-- Bar(SSKSKK;2,3->0) passes split Gad(t=0, W=(2, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丨丘丘久丘丘丧丘丘丧丘丘丞中九丮九丘丞丘丨丘丘丨丘丘乄丘丘丧丘") ⟫ʷ ≈ ⟪ (ℓ "丘丨丘丘久丘丘丧丘丘丧丘丘丞中九丮九丘丞丘丨丘丘丨丘丘乄丘丘丧丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丨丘丘久丘丘丧丘丘丧丘丘丞中九丮九丘丞丘丨丘丘丨丘丘乄丘丘丧丘") (ℓ "丘丨丘丘久丘丘丧丘丘丧丘丘丞中九丮九丘丞丘丨丘丘丨丘丘乄丘丘丧丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 0 q49 ∷
   rw 3 q50 ∷
   rw 6 q51 ∷
   rw 9 q51 ∷
   rw 12 q52 ∷
   rw 20 q49 ∷
   rw 23 q49 ∷
   rw 26 q53 ∷
   rw 29 q51 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = sE 2975 lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩-2
  q55 : Eqn
  q55 = sE 2949 lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩
  q56 : Eqn
  q56 = sE 2975 lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩-2

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X0 X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X0 X2 X3]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丌丘丞与丐丽习举习丑丏丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞与丐丽习举习丑丏丌丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丌丘丞与丐丽习举习丑丏丌丘丞") (ℓ "丌丘丞与丐丽习举习丑丏丌丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q54 ∷
   rw 0 q55 ∷
   rw⁻ 0 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = sE 2948 lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩

-- pass [CCZ123] [X0 X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X0 X2 X3]: 3 steps
lem-pass-CCZ123-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 : ⟪ (ℓ "乜丌丘丞与丐丽习举习丑丏丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞与丐丽习举习丑丏丌丘丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 = derive (ℓ "乜丌丘丞与丐丽习举习丑丏丌丘丞") (ℓ "丌丘丞与丐丽习举习丑丏丌丘丞乜")
  (rw 1 q54 ∷
   rw 0 q57 ∷
   rw⁻ 0 q56 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = sE 2950 lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X0 X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X0 X2 X3]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丌丘丞与丐丽习举习丑丏丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞与丐丽习举习丑丏丌丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丌丘丞与丐丽习举习丑丏丌丘丞") (ℓ "丌丘丞与丐丽习举习丑丏丌丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 31 q54 ∷
   rw 0 q58 ∷
   rw⁻ 0 q56 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = sE 2941 lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X0 X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X0 X2 X3]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丌丘丞与丐丽习举习丑丏丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞与丐丽习举习丑丏丌丘丞丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X2-X3 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丌丘丞与丐丽习举习丑丏丌丘丞") (ℓ "丌丘丞与丐丽习举习丑丏丌丘丞丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 29 q54 ∷
   rw 0 q59 ∷
   rw⁻ 0 q56 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = sE 2972 lem-ca-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩-3
  q61 : Eqn
  q61 = sE 2958 lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩
  q62 : Eqn
  q62 = sE 2972 lem-ca-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩-3

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X0 X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞丕丗且且义乣乊乣丕丕世且丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞丕丗且且义乣乊乣丕丕世且丌丞") (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 29 q60 ∷
   rw 0 q61 ∷
   rw⁻ 0 q62 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = sE 2955 lem-CCZ⟨321⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩

-- pass [CCZ123] [X0 X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0 X3]: 3 steps
lem-pass-CCZ123-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : ⟪ (ℓ "乜丌丞丕丗且且义乣乊乣丕丕世且丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = derive (ℓ "乜丌丞丕丗且且义乣乊乣丕丕世且丌丞") (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞乜")
  (rw 1 q60 ∷
   rw 0 q63 ∷
   rw⁻ 0 q62 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = sE 2965 lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X0 X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0 X3]: 3 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丌丞丕丗且且义乣乊乣丕丕世且丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丌丞丕丗且且义乣乊乣丕丕世且丌丞") (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 31 q60 ∷
   rw 0 q64 ∷
   rw⁻ 0 q62 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = sE 2964 lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X0 X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丞丕丗且且义乣乊乣丕丕世且丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丞丕丗且且义乣乊乣丕丕世且丌丞") (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 29 q60 ∷
   rw 0 q65 ∷
   rw⁻ 0 q62 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = sE 2940 lem-b2g-0011PP2
  q67 : Eqn
  q67 = sE 1002 lem-AXIOM-LF-at0321
  q68 : Eqn
  q68 = sE 2966 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3
  q69 : Eqn
  q69 = sE 2978 lem-pass-TOFF123-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3
  q70 : Eqn
  q70 = sE 2968 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3
  q71 : Eqn
  q71 = sE 2967 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3
  q72 : Eqn
  q72 = sE 1002 lem-AXIOM-LF-at0321
  q73 : Eqn
  q73 = sE 2940 lem-b2g-0011PP2

-- far CS03 CS03 CK30 CS03 CX32 CS02 CS02 CS02 .. 0011PP2 sep 3: 9 steps
lem-far-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02-··-0011PP2-sep-3 : ⟪ (ℓ "中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临丘丞乣义乣乊丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞乣义乣乊丘丞中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临") ⟫ʷ
lem-far-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02-··-0011PP2-sep-3 = derive (ℓ "中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临丘丞乣义乣乊丘丞") (ℓ "丘丞乣义乣乊丘丞中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临")
  (rw 80 q66 ∷
   rw 0 q67 ∷
   rw 62 q68 ∷
   rw 61 q69 ∷
   rw 30 q70 ∷
   rw 29 q69 ∷
   rw 0 q71 ∷
   rw⁻ 14 q72 ∷
   rw⁻ 0 q73 ∷ []) Eq.refl
