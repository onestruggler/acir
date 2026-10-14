------------------------------------------------------------------------
-- Presentations of groups
--
-- Bian and Selinger's Clifford+CS relations: the rules on their own
-- wires, padded by Circuit.TopPad, give the same congruence as
-- Syntactics' rules at every width, lifted by Circuit.Base's
-- Lift-Relation
--
-- An instance of Circuit.TopPad.Equivalence, as Symmetric.TopPad is:
-- each rule that Syntactics states at every width is here stated on its
-- own wires only (its name with ᴮ), its padded form is that rule with
-- idle wires on top (↓), and SameRules says, rule by rule, that the two
-- relations have the same rules.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford+CS.TopPad where

open import Data.Nat using (ℕ)
open import Notations
open import Word.Base

import Circuit.TopPad
import Circuit.TopPad.Equivalence
import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics

open Circuit.TopPad Gate using (_⇓)

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The rules on their own wires, padded by Top-Pad

infix 4 _Base,_===_
data _Base,_===_ : (n : ℕ) → WRel (Gen n) where
  order-Iᴮ : 0 Base, iI • iI • iI • iI === ε
  order-Sᴮ : 1 Base, S • S • S • S === ε
  order-Kᴮ : 1 Base, K • K === iI • iI • iI
  order-SKᴮ : 1 Base, S • K • S • K • S • K === iI • iI • iI
  order-CSᴮ : 2 Base, CS • CS • CS • CS === ε
  comm-CS-S₀ᴮ : 2 Base, CS • S === S • CS
  comm-CS-S₁ᴮ : 2 Base, CS • S ↑ === S ↑ • CS
  X-CS₀ᴮ : 2 Base, X • CS === CS • CS • CS • X • S ↑
  X-CS₁ᴮ : 2 Base, X ↑ • CS === CS • CS • CS • X ↑ • S
  CS-K₀ᴮ : 2 Base, CS • K • CS • K • S === S • K • CS • K • CS
  CS-K₁ᴮ : 2 Base, CS • K ↑ • CS • K ↑ • S ↑ === S ↑ • K ↑ • CS • K ↑ • CS
  comm-CS↑-CSᴮ : 3 Base, CS ↑ • CS === CS • CS ↑
  rel-266ᴮ : 3 Base, CX₁₀ • CX₀₁ • CS ↑ • CX₀₁ • CX₁₀ ===
        CX₁₂ • CX₂₁ • CS • CX₂₁ • CX₁₂
  rel-267ᴮ : 3 Base, CX₁₀ • CX₀₁ • CS ↑ • CS ↑ • CX₀₁ • CX₁₀ ===
        CX₀₁ • CS ↑ • CS ↑ • CX₀₁ • CS ↑ • CS ↑
  rel-268ᴮ : 3 Base, CS ↑ • CX₀₁ • CS ↑ • CS ↑ • CS ↑ • CX₀₁ ===
        CS • CX₂₁ • CS • CS • CS • CX₂₁
  rel-269ᴮ : 3 Base, CS ↑ • K ↑ • CS ↑ • K ↑ • CS • K ↑ • CS ===
        CS • K ↑ • CS • K ↑ • CS ↑ • K ↑ • CS ↑
  rel-272ᴮ : 3 Base,
        CS ↑ • K ↑ • CS ↑ • CS ↑ • CS ↑ • K ↑ • CS • K ↑ • CS ↑ ===
        CS • K ↑ • CS • CS • CS • K ↑ • CS ↑ • K ↑ • CS

module TP = Circuit.TopPad.Top-Pad Gate _Base,_===_
module E  = Circuit.TopPad.Equivalence.Lift≅Top-Pad Gate _SRel,_===_ _Base,_===_

open E public using (_TRel,_===_ ; _⊢ᵀ_≈_ ; _⊢ᴸ_≈_)

-- Each rule on the bottom wires of every wider circuit: its words are
-- closed, so one wire wider they are the same words.

order-I↓ : n TRel, iI • iI • iI • iI === ε
order-I↓ {0}    = TP.srel order-Iᴮ
order-I↓ {₁₊ n} = TP.cong↓ order-I↓

order-S↓ : (₁₊ n) TRel, S • S • S • S === ε
order-S↓ {0}    = TP.srel order-Sᴮ
order-S↓ {₁₊ n} = TP.cong↓ order-S↓

order-K↓ : (₁₊ n) TRel, K • K === iI • iI • iI
order-K↓ {0}    = TP.srel order-Kᴮ
order-K↓ {₁₊ n} = TP.cong↓ order-K↓

order-SK↓ : (₁₊ n) TRel, S • K • S • K • S • K === iI • iI • iI
order-SK↓ {0}    = TP.srel order-SKᴮ
order-SK↓ {₁₊ n} = TP.cong↓ order-SK↓

order-CS↓ : (₂₊ n) TRel, CS • CS • CS • CS === ε
order-CS↓ {0}    = TP.srel order-CSᴮ
order-CS↓ {₁₊ n} = TP.cong↓ order-CS↓

comm-CS-S₀↓ : (₂₊ n) TRel, CS • S === S • CS
comm-CS-S₀↓ {0}    = TP.srel comm-CS-S₀ᴮ
comm-CS-S₀↓ {₁₊ n} = TP.cong↓ comm-CS-S₀↓

comm-CS-S₁↓ : (₂₊ n) TRel, CS • S ↑ === S ↑ • CS
comm-CS-S₁↓ {0}    = TP.srel comm-CS-S₁ᴮ
comm-CS-S₁↓ {₁₊ n} = TP.cong↓ comm-CS-S₁↓

X-CS₀↓ : (₂₊ n) TRel, X • CS === CS • CS • CS • X • S ↑
X-CS₀↓ {0}    = TP.srel X-CS₀ᴮ
X-CS₀↓ {₁₊ n} = TP.cong↓ X-CS₀↓

X-CS₁↓ : (₂₊ n) TRel, X ↑ • CS === CS • CS • CS • X ↑ • S
X-CS₁↓ {0}    = TP.srel X-CS₁ᴮ
X-CS₁↓ {₁₊ n} = TP.cong↓ X-CS₁↓

CS-K₀↓ : (₂₊ n) TRel, CS • K • CS • K • S === S • K • CS • K • CS
CS-K₀↓ {0}    = TP.srel CS-K₀ᴮ
CS-K₀↓ {₁₊ n} = TP.cong↓ CS-K₀↓

CS-K₁↓ : (₂₊ n) TRel, CS • K ↑ • CS • K ↑ • S ↑ === S ↑ • K ↑ • CS • K ↑ • CS
CS-K₁↓ {0}    = TP.srel CS-K₁ᴮ
CS-K₁↓ {₁₊ n} = TP.cong↓ CS-K₁↓

comm-CS↑-CS↓ : (₃₊ n) TRel, CS ↑ • CS === CS • CS ↑
comm-CS↑-CS↓ {0}    = TP.srel comm-CS↑-CSᴮ
comm-CS↑-CS↓ {₁₊ n} = TP.cong↓ comm-CS↑-CS↓

rel-266↓ : (₃₊ n) TRel, CX₁₀ • CX₀₁ • CS ↑ • CX₀₁ • CX₁₀ ===
      CX₁₂ • CX₂₁ • CS • CX₂₁ • CX₁₂
rel-266↓ {0}    = TP.srel rel-266ᴮ
rel-266↓ {₁₊ n} = TP.cong↓ rel-266↓

rel-267↓ : (₃₊ n) TRel, CX₁₀ • CX₀₁ • CS ↑ • CS ↑ • CX₀₁ • CX₁₀ ===
      CX₀₁ • CS ↑ • CS ↑ • CX₀₁ • CS ↑ • CS ↑
rel-267↓ {0}    = TP.srel rel-267ᴮ
rel-267↓ {₁₊ n} = TP.cong↓ rel-267↓

rel-268↓ : (₃₊ n) TRel, CS ↑ • CX₀₁ • CS ↑ • CS ↑ • CS ↑ • CX₀₁ ===
      CS • CX₂₁ • CS • CS • CS • CX₂₁
rel-268↓ {0}    = TP.srel rel-268ᴮ
rel-268↓ {₁₊ n} = TP.cong↓ rel-268↓

rel-269↓ : (₃₊ n) TRel, CS ↑ • K ↑ • CS ↑ • K ↑ • CS • K ↑ • CS ===
      CS • K ↑ • CS • K ↑ • CS ↑ • K ↑ • CS ↑
rel-269↓ {0}    = TP.srel rel-269ᴮ
rel-269↓ {₁₊ n} = TP.cong↓ rel-269↓

rel-272↓ : (₃₊ n) TRel,
      CS ↑ • K ↑ • CS ↑ • CS ↑ • CS ↑ • K ↑ • CS • K ↑ • CS ↑ ===
      CS • K ↑ • CS • CS • CS • K ↑ • CS ↑ • K ↑ • CS
rel-272↓ {0}    = TP.srel rel-272ᴮ
rel-272↓ {₁₊ n} = TP.cong↓ rel-272↓

------------------------------------------------------------------------
-- The two have the same rules

same : E.SameRules
same = record { pad = pad ; unpad = unpad ; srel-⇓ = srel-⇓ }
  where
  pad : n SRel, w === v → n ⊢ᵀ w ≈ v
  pad order-I = PB.axiom order-I↓
  pad order-S = PB.axiom order-S↓
  pad order-K = PB.axiom order-K↓
  pad order-SK = PB.axiom order-SK↓
  pad order-CS = PB.axiom order-CS↓
  pad comm-CS-S₀ = PB.axiom comm-CS-S₀↓
  pad comm-CS-S₁ = PB.axiom comm-CS-S₁↓
  pad X-CS₀ = PB.axiom X-CS₀↓
  pad X-CS₁ = PB.axiom X-CS₁↓
  pad CS-K₀ = PB.axiom CS-K₀↓
  pad CS-K₁ = PB.axiom CS-K₁↓
  pad comm-CS↑-CS = PB.axiom comm-CS↑-CS↓
  pad rel-266 = PB.axiom rel-266↓
  pad rel-267 = PB.axiom rel-267↓
  pad rel-268 = PB.axiom rel-268↓
  pad rel-269 = PB.axiom rel-269↓
  pad rel-272 = PB.axiom rel-272↓

  unpad : n Base, w === v → n ⊢ᴸ w ≈ v
  unpad order-Iᴮ = PB.axiom (srel order-I)
  unpad order-Sᴮ = PB.axiom (srel order-S)
  unpad order-Kᴮ = PB.axiom (srel order-K)
  unpad order-SKᴮ = PB.axiom (srel order-SK)
  unpad order-CSᴮ = PB.axiom (srel order-CS)
  unpad comm-CS-S₀ᴮ = PB.axiom (srel comm-CS-S₀)
  unpad comm-CS-S₁ᴮ = PB.axiom (srel comm-CS-S₁)
  unpad X-CS₀ᴮ = PB.axiom (srel X-CS₀)
  unpad X-CS₁ᴮ = PB.axiom (srel X-CS₁)
  unpad CS-K₀ᴮ = PB.axiom (srel CS-K₀)
  unpad CS-K₁ᴮ = PB.axiom (srel CS-K₁)
  unpad comm-CS↑-CSᴮ = PB.axiom (srel comm-CS↑-CS)
  unpad rel-266ᴮ = PB.axiom (srel rel-266)
  unpad rel-267ᴮ = PB.axiom (srel rel-267)
  unpad rel-268ᴮ = PB.axiom (srel rel-268)
  unpad rel-269ᴮ = PB.axiom (srel rel-269)
  unpad rel-272ᴮ = PB.axiom (srel rel-272)

  srel-⇓ : n SRel, w === v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓
  srel-⇓ order-I = PB.axiom (srel order-I)
  srel-⇓ order-S = PB.axiom (srel order-S)
  srel-⇓ order-K = PB.axiom (srel order-K)
  srel-⇓ order-SK = PB.axiom (srel order-SK)
  srel-⇓ order-CS = PB.axiom (srel order-CS)
  srel-⇓ comm-CS-S₀ = PB.axiom (srel comm-CS-S₀)
  srel-⇓ comm-CS-S₁ = PB.axiom (srel comm-CS-S₁)
  srel-⇓ X-CS₀ = PB.axiom (srel X-CS₀)
  srel-⇓ X-CS₁ = PB.axiom (srel X-CS₁)
  srel-⇓ CS-K₀ = PB.axiom (srel CS-K₀)
  srel-⇓ CS-K₁ = PB.axiom (srel CS-K₁)
  srel-⇓ comm-CS↑-CS = PB.axiom (srel comm-CS↑-CS)
  srel-⇓ rel-266 = PB.axiom (srel rel-266)
  srel-⇓ rel-267 = PB.axiom (srel rel-267)
  srel-⇓ rel-268 = PB.axiom (srel rel-268)
  srel-⇓ rel-269 = PB.axiom (srel rel-269)
  srel-⇓ rel-272 = PB.axiom (srel rel-272)

------------------------------------------------------------------------
-- So the congruences coincide, and the identity is a group isomorphism

open E.Equivalent same public using (lr⇒tp ; tp⇒lr)
open E.Equivalent.Iso same grouplike public using (glᵀ ; lr≅tp)
