------------------------------------------------------------------------
-- Presentations of groups
--
-- Clément's Figure 4 with the swap rules of Remark 1: the rules on
-- their own wires, padded by Circuit.TopPad, give the same congruence
-- as Syntactics' rules at every width, lifted by Circuit.Base's
-- Lift-Relation
--
-- An instance of Circuit.TopPad.Equivalence, as Symmetric.TopPad is:
-- each rule that Syntactics states at every width is here stated on its
-- own wires only (its name with ᴮ), its padded form is that rule with
-- idle wires on top (↓), and SameRules says, rule by rule, that the two
-- relations have the same rules. (19), the schema box-Z, is stated on
-- exactly the wires its box holds already, so it is a rule on its own
-- wires as it stands; with an idle wire on top it is TopWeakening's
-- top-cong.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.TopPad where

open import Data.Nat using (ℕ)
open import Notations
open import Word.Base

import Circuit.TopPad
import Circuit.TopPad.Equivalence
import Presentation.Base as PB

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
import Examples.Groups.Real-Clifford+CH.TopWeakening as TW

open Circuit.TopPad Gate using (_↧ ; _⇓)

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The rules on their own wires, padded by Top-Pad

infix 4 _Base,_===_
data _Base,_===_ : (n : ℕ) → WRel (Gen n) where
  order-Hᴮ : 1 Base, H • H === ε
  order-Zᴮ : 1 Base, Z • Z === ε
  order-HZᴮ : 1 Base, (H • Z) ^ 8 === ε
  order-CZᴮ : 2 Base, CZ • CZ === ε
  order-CHᴮ : 2 Base, CH • CH === ε
  merge-CZᴮ : 2 Base, CZ • °CZ === Z ↓
  merge-CHᴮ : 2 Base, CH • °CH === H ↓
  comm-CZ-Exᴮ : 2 Base, CZ • Ex === Ex • CZ
  comm-CH-°CZᴮ : 2 Base, CH • °CZ === °CZ • CH
  slide-CHᴮ : 2 Base, CH • H ↑ • Z ↑ • CH • H ↑ === H ↑ • Z ↑ • CH • H ↑ • CH
  comm-CZ↑-CZ↓ᴮ : 3 Base, CZ ↑ • CZ ↓ === CZ ↓ • CZ ↑
  comm-CZ↑-CH↓ᴮ : 3 Base, CZ ↑ • CH ↓ === CH ↓ • CZ ↑
  symm-controlsᴮ : 3 Base, CH ↓ • CZ₂₀ • CH ↓ • CZ₂₀ ===
        CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓
  square-CCZXᴮ : 3 Base, (CH ↓ • CZ₂₀) ^ 4 === CZ ↑
  comm-°CZ₂₀-CHᴮ : 3 Base, °CZ₂₀ • CH ↓ • CZ₂₀ • CH ↓ ===
        CH ↓ • CZ₂₀ • CH ↓ • °CZ₂₀
  comm-°CZ₂₀-HHᴮ : 3 Base, °CZ₂₀ • CH ↓ • CH ↑ • CH ↓ ===
        CH ↓ • CH ↑ • CH ↓ • °CZ₂₀
  conj-PPᴮ : 3 Base, CZ ↑ • PP ↓ === PP ↓ • CH ↑
  swap-orderᴮ : 2 Base, Ex • Ex === ε
  swap-Zᴮ : 2 Base, Z ↑ • Ex === Ex • Z ↓
  swap-Hᴮ : 2 Base, H ↑ • Ex === Ex • H ↓
  swap-CZᴮ : 3 Base, CZ ↑ • Ex ↓ • Ex ↑ === Ex ↓ • Ex ↑ • CZ ↓
  swap-CHᴮ : 3 Base, CH ↑ • Ex ↓ • Ex ↑ === Ex ↓ • Ex ↑ • CH ↓
  -- (19) is already on its own wires: the box holds every wire.
  box-Zᴮ : ∀ k → (₁₊ (₄₊ k)) Base, Z ↓ • Λ□ (₄₊ k) === Λ□ (₄₊ k) • Z ↓

module TP = Circuit.TopPad.Top-Pad Gate _Base,_===_
module E  = Circuit.TopPad.Equivalence.Lift≅Top-Pad Gate _SRel,_===_ _Base,_===_

open E public using (_TRel,_===_ ; _⊢ᵀ_≈_ ; _⊢ᴸ_≈_)

-- Each rule on the bottom wires of every wider circuit: its words are
-- closed, so one wire wider they are the same words.

order-H↓ : (₁₊ n) TRel, H • H === ε
order-H↓ {0}    = TP.srel order-Hᴮ
order-H↓ {₁₊ n} = TP.cong↓ order-H↓

order-Z↓ : (₁₊ n) TRel, Z • Z === ε
order-Z↓ {0}    = TP.srel order-Zᴮ
order-Z↓ {₁₊ n} = TP.cong↓ order-Z↓

order-HZ↓ : (₁₊ n) TRel, (H • Z) ^ 8 === ε
order-HZ↓ {0}    = TP.srel order-HZᴮ
order-HZ↓ {₁₊ n} = TP.cong↓ order-HZ↓

order-CZ↓ : (₂₊ n) TRel, CZ • CZ === ε
order-CZ↓ {0}    = TP.srel order-CZᴮ
order-CZ↓ {₁₊ n} = TP.cong↓ order-CZ↓

order-CH↓ : (₂₊ n) TRel, CH • CH === ε
order-CH↓ {0}    = TP.srel order-CHᴮ
order-CH↓ {₁₊ n} = TP.cong↓ order-CH↓

merge-CZ↓ : (₂₊ n) TRel, CZ • °CZ === Z ↓
merge-CZ↓ {0}    = TP.srel merge-CZᴮ
merge-CZ↓ {₁₊ n} = TP.cong↓ merge-CZ↓

merge-CH↓ : (₂₊ n) TRel, CH • °CH === H ↓
merge-CH↓ {0}    = TP.srel merge-CHᴮ
merge-CH↓ {₁₊ n} = TP.cong↓ merge-CH↓

comm-CZ-Ex↓ : (₂₊ n) TRel, CZ • Ex === Ex • CZ
comm-CZ-Ex↓ {0}    = TP.srel comm-CZ-Exᴮ
comm-CZ-Ex↓ {₁₊ n} = TP.cong↓ comm-CZ-Ex↓

comm-CH-°CZ↓ : (₂₊ n) TRel, CH • °CZ === °CZ • CH
comm-CH-°CZ↓ {0}    = TP.srel comm-CH-°CZᴮ
comm-CH-°CZ↓ {₁₊ n} = TP.cong↓ comm-CH-°CZ↓

slide-CH↓ : (₂₊ n) TRel, CH • H ↑ • Z ↑ • CH • H ↑ ===
      H ↑ • Z ↑ • CH • H ↑ • CH
slide-CH↓ {0}    = TP.srel slide-CHᴮ
slide-CH↓ {₁₊ n} = TP.cong↓ slide-CH↓

comm-CZ↑-CZ↓↓ : (₃₊ n) TRel, CZ ↑ • CZ ↓ === CZ ↓ • CZ ↑
comm-CZ↑-CZ↓↓ {0}    = TP.srel comm-CZ↑-CZ↓ᴮ
comm-CZ↑-CZ↓↓ {₁₊ n} = TP.cong↓ comm-CZ↑-CZ↓↓

comm-CZ↑-CH↓↓ : (₃₊ n) TRel, CZ ↑ • CH ↓ === CH ↓ • CZ ↑
comm-CZ↑-CH↓↓ {0}    = TP.srel comm-CZ↑-CH↓ᴮ
comm-CZ↑-CH↓↓ {₁₊ n} = TP.cong↓ comm-CZ↑-CH↓↓

symm-controls↓ : (₃₊ n) TRel, CH ↓ • CZ₂₀ • CH ↓ • CZ₂₀ ===
      CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓
symm-controls↓ {0}    = TP.srel symm-controlsᴮ
symm-controls↓ {₁₊ n} = TP.cong↓ symm-controls↓

square-CCZX↓ : (₃₊ n) TRel, (CH ↓ • CZ₂₀) ^ 4 === CZ ↑
square-CCZX↓ {0}    = TP.srel square-CCZXᴮ
square-CCZX↓ {₁₊ n} = TP.cong↓ square-CCZX↓

comm-°CZ₂₀-CH↓ : (₃₊ n) TRel, °CZ₂₀ • CH ↓ • CZ₂₀ • CH ↓ ===
      CH ↓ • CZ₂₀ • CH ↓ • °CZ₂₀
comm-°CZ₂₀-CH↓ {0}    = TP.srel comm-°CZ₂₀-CHᴮ
comm-°CZ₂₀-CH↓ {₁₊ n} = TP.cong↓ comm-°CZ₂₀-CH↓

comm-°CZ₂₀-HH↓ : (₃₊ n) TRel, °CZ₂₀ • CH ↓ • CH ↑ • CH ↓ ===
      CH ↓ • CH ↑ • CH ↓ • °CZ₂₀
comm-°CZ₂₀-HH↓ {0}    = TP.srel comm-°CZ₂₀-HHᴮ
comm-°CZ₂₀-HH↓ {₁₊ n} = TP.cong↓ comm-°CZ₂₀-HH↓

conj-PP↓ : (₃₊ n) TRel, CZ ↑ • PP ↓ === PP ↓ • CH ↑
conj-PP↓ {0}    = TP.srel conj-PPᴮ
conj-PP↓ {₁₊ n} = TP.cong↓ conj-PP↓

swap-order↓ : (₂₊ n) TRel, Ex • Ex === ε
swap-order↓ {0}    = TP.srel swap-orderᴮ
swap-order↓ {₁₊ n} = TP.cong↓ swap-order↓

swap-Z↓ : (₂₊ n) TRel, Z ↑ • Ex === Ex • Z ↓
swap-Z↓ {0}    = TP.srel swap-Zᴮ
swap-Z↓ {₁₊ n} = TP.cong↓ swap-Z↓

swap-H↓ : (₂₊ n) TRel, H ↑ • Ex === Ex • H ↓
swap-H↓ {0}    = TP.srel swap-Hᴮ
swap-H↓ {₁₊ n} = TP.cong↓ swap-H↓

swap-CZ↓ : (₃₊ n) TRel, CZ ↑ • Ex ↓ • Ex ↑ === Ex ↓ • Ex ↑ • CZ ↓
swap-CZ↓ {0}    = TP.srel swap-CZᴮ
swap-CZ↓ {₁₊ n} = TP.cong↓ swap-CZ↓

swap-CH↓ : (₃₊ n) TRel, CH ↑ • Ex ↓ • Ex ↑ === Ex ↓ • Ex ↑ • CH ↓
swap-CH↓ {0}    = TP.srel swap-CHᴮ
swap-CH↓ {₁₊ n} = TP.cong↓ swap-CH↓

-- TopWeakening's top is ⇓ (its own copy of _↧), so (19) with an idle
-- wire on top is TopWeakening's top-cong.
↧≡ : (g : Gen n) → g TW.↧ ≡ g ↧
↧≡ (gate₀ h) = Eq.refl
↧≡ (gate₁ h) = Eq.refl
↧≡ (gate₂ h) = Eq.refl
↧≡ (g ↥)     = Eq.cong _↥ (↧≡ g)

top≡⇓ : (w : Circuit n) → TW.top w ≡ w ⇓
top≡⇓ [ g ]ʷ  = Eq.cong [_]ʷ (↧≡ g)
top≡⇓ ε       = Eq.refl
top≡⇓ (u • t) = Eq.cong₂ _•_ (top≡⇓ u) (top≡⇓ t)

top-⇓ : (₁₊ n) ⊢ TW.top w ≈ TW.top v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓
top-⇓ {w = w} {v} e =
  Eq.subst₂ (λ a b → _ ⊢ᴸ a ≈ b) (top≡⇓ w) (top≡⇓ v) e

------------------------------------------------------------------------
-- The two have the same rules

same : E.SameRules
same = record { pad = pad ; unpad = unpad ; srel-⇓ = srel-⇓ }
  where
  pad : n SRel, w === v → n ⊢ᵀ w ≈ v
  pad order-H = PB.axiom order-H↓
  pad order-Z = PB.axiom order-Z↓
  pad order-HZ = PB.axiom order-HZ↓
  pad order-CZ = PB.axiom order-CZ↓
  pad order-CH = PB.axiom order-CH↓
  pad merge-CZ = PB.axiom merge-CZ↓
  pad merge-CH = PB.axiom merge-CH↓
  pad comm-CZ-Ex = PB.axiom comm-CZ-Ex↓
  pad comm-CH-°CZ = PB.axiom comm-CH-°CZ↓
  pad slide-CH = PB.axiom slide-CH↓
  pad comm-CZ↑-CZ↓ = PB.axiom comm-CZ↑-CZ↓↓
  pad comm-CZ↑-CH↓ = PB.axiom comm-CZ↑-CH↓↓
  pad symm-controls = PB.axiom symm-controls↓
  pad square-CCZX = PB.axiom square-CCZX↓
  pad comm-°CZ₂₀-CH = PB.axiom comm-°CZ₂₀-CH↓
  pad comm-°CZ₂₀-HH = PB.axiom comm-°CZ₂₀-HH↓
  pad conj-PP = PB.axiom conj-PP↓
  pad swap-order = PB.axiom swap-order↓
  pad swap-Z = PB.axiom swap-Z↓
  pad swap-H = PB.axiom swap-H↓
  pad swap-CZ = PB.axiom swap-CZ↓
  pad swap-CH = PB.axiom swap-CH↓
  pad (box-Z k) = PB.axiom (TP.srel (box-Zᴮ k))

  unpad : n Base, w === v → n ⊢ᴸ w ≈ v
  unpad order-Hᴮ = PB.axiom (srel order-H)
  unpad order-Zᴮ = PB.axiom (srel order-Z)
  unpad order-HZᴮ = PB.axiom (srel order-HZ)
  unpad order-CZᴮ = PB.axiom (srel order-CZ)
  unpad order-CHᴮ = PB.axiom (srel order-CH)
  unpad merge-CZᴮ = PB.axiom (srel merge-CZ)
  unpad merge-CHᴮ = PB.axiom (srel merge-CH)
  unpad comm-CZ-Exᴮ = PB.axiom (srel comm-CZ-Ex)
  unpad comm-CH-°CZᴮ = PB.axiom (srel comm-CH-°CZ)
  unpad slide-CHᴮ = PB.axiom (srel slide-CH)
  unpad comm-CZ↑-CZ↓ᴮ = PB.axiom (srel comm-CZ↑-CZ↓)
  unpad comm-CZ↑-CH↓ᴮ = PB.axiom (srel comm-CZ↑-CH↓)
  unpad symm-controlsᴮ = PB.axiom (srel symm-controls)
  unpad square-CCZXᴮ = PB.axiom (srel square-CCZX)
  unpad comm-°CZ₂₀-CHᴮ = PB.axiom (srel comm-°CZ₂₀-CH)
  unpad comm-°CZ₂₀-HHᴮ = PB.axiom (srel comm-°CZ₂₀-HH)
  unpad conj-PPᴮ = PB.axiom (srel conj-PP)
  unpad swap-orderᴮ = PB.axiom (srel swap-order)
  unpad swap-Zᴮ = PB.axiom (srel swap-Z)
  unpad swap-Hᴮ = PB.axiom (srel swap-H)
  unpad swap-CZᴮ = PB.axiom (srel swap-CZ)
  unpad swap-CHᴮ = PB.axiom (srel swap-CH)
  unpad (box-Zᴮ k) = PB.axiom (srel (box-Z k))

  srel-⇓ : n SRel, w === v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓
  srel-⇓ order-H = PB.axiom (srel order-H)
  srel-⇓ order-Z = PB.axiom (srel order-Z)
  srel-⇓ order-HZ = PB.axiom (srel order-HZ)
  srel-⇓ order-CZ = PB.axiom (srel order-CZ)
  srel-⇓ order-CH = PB.axiom (srel order-CH)
  srel-⇓ merge-CZ = PB.axiom (srel merge-CZ)
  srel-⇓ merge-CH = PB.axiom (srel merge-CH)
  srel-⇓ comm-CZ-Ex = PB.axiom (srel comm-CZ-Ex)
  srel-⇓ comm-CH-°CZ = PB.axiom (srel comm-CH-°CZ)
  srel-⇓ slide-CH = PB.axiom (srel slide-CH)
  srel-⇓ comm-CZ↑-CZ↓ = PB.axiom (srel comm-CZ↑-CZ↓)
  srel-⇓ comm-CZ↑-CH↓ = PB.axiom (srel comm-CZ↑-CH↓)
  srel-⇓ symm-controls = PB.axiom (srel symm-controls)
  srel-⇓ square-CCZX = PB.axiom (srel square-CCZX)
  srel-⇓ comm-°CZ₂₀-CH = PB.axiom (srel comm-°CZ₂₀-CH)
  srel-⇓ comm-°CZ₂₀-HH = PB.axiom (srel comm-°CZ₂₀-HH)
  srel-⇓ conj-PP = PB.axiom (srel conj-PP)
  srel-⇓ swap-order = PB.axiom (srel swap-order)
  srel-⇓ swap-Z = PB.axiom (srel swap-Z)
  srel-⇓ swap-H = PB.axiom (srel swap-H)
  srel-⇓ swap-CZ = PB.axiom (srel swap-CZ)
  srel-⇓ swap-CH = PB.axiom (srel swap-CH)
  srel-⇓ (box-Z k) = top-⇓ (TW.top-cong (PB.axiom (srel (box-Z k))))

------------------------------------------------------------------------
-- So the congruences coincide, and the identity is a group isomorphism

open E.Equivalent same public using (lr⇒tp ; tp⇒lr)
open E.Equivalent.Iso same grouplike public using (glᵀ ; lr≅tp)
