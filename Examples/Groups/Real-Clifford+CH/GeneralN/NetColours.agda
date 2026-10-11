------------------------------------------------------------------------
-- Presentations of groups
--
-- Colourings through swap networks (Clément, Appendix E.5)
--
-- A colouring `negsB s` (X on the wires where s is false) conjugated by
-- a network is the colouring with its bits permuted along the network
-- (`net-negs`, `swW`); two colourings compose to one, X where exactly
-- one of them has it (`negs-xor`, `combine`), so a colouring of a
-- colouring is a colouring (`col-col`) and two colourings of gates
-- commute as soon as the gates do in their relative colouring
-- (`col-pair`, `col-pair′`).  Moved out of BoxAnywhere, which needs
-- completeness below, so that the placement layer (Placed) does not.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.NetColours where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (ℕ)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊)

import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; X²)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; φ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; negs² ; revS ; swapAt-negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- A colouring through a network

-- The permutation of the bits along a swap, and along a network.
swG : S.Gen n → Bits n → Bits n
swG (S.gate₀ ())
swG (S.gate₁ ())
swG (S.gate₂ S.σ-gate) (a ∷ b ∷ t) = b ∷ a ∷ t
swG (g S.↥)            (a ∷ t)     = a ∷ swG g t

swW : Word (S.Gen n) → Bits n → Bits n
swW [ g ]ʷ  t = swG g t
swW ε       t = t
swW (u • v) t = swW u (swW v t)

gen-negs : ∀ (g : S.Gen n) (t : Bits n) → n ⊢ φ g • negsB t • φ g ≈ negsB (swG g t)
gen-negs (S.gate₀ ()) t
gen-negs (S.gate₁ ()) t
gen-negs (S.gate₂ S.σ-gate) (a ∷ b ∷ t) = swapAt-negsB 0 (a ∷ b ∷ t)
gen-negs {₁₊ n} (g S.↥) (true ∷ t) = lemma-cong↑ _ _ (gen-negs g t)
gen-negs {₁₊ n} (g S.↥) (false ∷ t) = begin
  G • (X • R) • G        ≈⟨ trans (sym assoc) (front _ (trans (sym assoc) (front _ (sym (X-↑ (φ g)))))) ⟩
  ((X • G) • R) • G      ≈⟨ by-passoc (((□ • □) • □) • □) (□ • (□ • □ • □)) Eq.refl ⟩
  X • (G • R • G)        ≈⟨ back _ (lemma-cong↑ _ _ (gen-negs g t)) ⟩
  X • negsB (swG g t) ↑ ∎
  where
  open Tools ((₁₊ n) VRel,_===_)
  G R : Circuit (₁₊ n)
  G = φ g ↑
  R = negsB t ↑

net-negs : ∀ (w : Word (S.Gen n)) (t : Bits n) → n ⊢ net w • negsB t • net (revS w) ≈ negsB (swW w t)
net-negs [ g ]ʷ  t = gen-negs g t
net-negs {n} ε   t = trans left-unit right-unit
  where open Tools (n VRel,_===_)
net-negs {n} (u • v) t = begin
  (net u • net v) • negsB t • (net (revS v) • net (revS u))
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
  net u • (net v • negsB t • net (revS v)) • net (revS u)
    ≈⟨ back _ (front _ (net-negs v t)) ⟩
  net u • negsB (swW v t) • net (revS u)
    ≈⟨ net-negs u (swW v t) ⟩
  negsB (swW u (swW v t)) ∎
  where open Tools (n VRel,_===_)

------------------------------------------------------------------------
-- Two colourings compose

-- The colouring with X where exactly one of the two has it.
_⇔_ : Bool → Bool → Bool
true  ⇔ b = b
false ⇔ b = not b

combine : Bits n → Bits n → Bits n
combine []      []      = []
combine (a ∷ x) (b ∷ y) = (a ⇔ b) ∷ combine x y

negs-xor : ∀ (x y : Bits n) → n ⊢ negsB x • negsB y ≈ negsB (combine x y)
negs-xor [] [] = left-unit
  where open Tools (0 VRel,_===_)
negs-xor {₁₊ n} (true ∷ x) (true ∷ y) = lemma-cong↑ _ _ (negs-xor x y)
negs-xor {₁₊ n} (true ∷ x) (false ∷ y) = begin
  negsB x ↑ • X • negsB y ↑        ≈⟨ trans (sym assoc) (trans (front _ (sym (X-↑ (negsB x)))) assoc) ⟩
  X • negsB x ↑ • negsB y ↑        ≈⟨ back _ (lemma-cong↑ _ _ (negs-xor x y)) ⟩
  X • negsB (combine x y) ↑ ∎
  where open Tools ((₁₊ n) VRel,_===_)
negs-xor {₁₊ n} (false ∷ x) (true ∷ y) = trans assoc (back _ (lemma-cong↑ _ _ (negs-xor x y)))
  where open Tools ((₁₊ n) VRel,_===_)
negs-xor {₁₊ n} (false ∷ x) (false ∷ y) = begin
  (X • negsB x ↑) • X • negsB y ↑      ≈⟨ trans assoc (back _ (trans (sym assoc) (front _ (sym (X-↑ (negsB x)))))) ⟩
  X • (X • negsB x ↑) • negsB y ↑      ≈⟨ trans (sym assoc) (trans (front _ (trans (sym assoc) (trans (front _ X²) left-unit))) (lemma-cong↑ _ _ (negs-xor x y))) ⟩
  negsB (combine x y) ↑ ∎
  where open Tools ((₁₊ n) VRel,_===_)

private
  ⇔-comm : ∀ a b → (a ⇔ b) ≡ (b ⇔ a)
  ⇔-comm true  true  = Eq.refl
  ⇔-comm true  false = Eq.refl
  ⇔-comm false true  = Eq.refl
  ⇔-comm false false = Eq.refl

  ⇔-cancel : ∀ a b → (a ⇔ (a ⇔ b)) ≡ b
  ⇔-cancel true  b     = Eq.refl
  ⇔-cancel false true  = Eq.refl
  ⇔-cancel false false = Eq.refl

  combine-comm : ∀ (x y : Bits n) → combine x y ≡ combine y x
  combine-comm []      []      = Eq.refl
  combine-comm (a ∷ x) (b ∷ y) = Eq.cong₂ _∷_ (⇔-comm a b) (combine-comm x y)

  combine-cancel : ∀ (x y : Bits n) → combine x (combine x y) ≡ y
  combine-cancel []      []      = Eq.refl
  combine-cancel (a ∷ x) (b ∷ y) = Eq.cong₂ _∷_ (⇔-cancel a b) (combine-cancel x y)

col-col : ∀ (x y : Bits n) (w : Circuit n) → n ⊢ col x (col y w) ≈ col (combine x y) w
col-col {n} x y w = begin
  negsB x • (negsB y • w • negsB y) • negsB x
    ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
  (negsB x • negsB y) • w • (negsB y • negsB x)
    ≈⟨ cong (negs-xor x y) (back _ (trans (negs-xor y x) (≡→≈ (Eq.cong negsB (combine-comm y x))))) ⟩
  negsB (combine x y) • w • negsB (combine x y) ∎
  where
  open Tools (n VRel,_===_)
  ≡→≈ : ∀ {p q : Circuit n} → p ≡ q → p ≈ q
  ≡→≈ Eq.refl = refl

-- Two colourings of w commute if every colouring of w commutes with w.
col-pair : ∀ (x y : Bits n) (w : Circuit n) →
           (∀ z → n ⊢ w • col z w ≈ col z w • w) → n ⊢ col x w • col y w ≈ col y w • col x w
col-pair {n} x y w h = begin
  col x w • col y w                    ≈⟨ back _ (sym e) ⟩
  col x w • col x (col z w)            ≈⟨ sym (col-• x w (col z w)) ⟩
  col x (w • col z w)                  ≈⟨ back _ (front _ (h z)) ⟩
  col x (col z w • w)                  ≈⟨ col-• x (col z w) w ⟩
  col x (col z w) • col x w            ≈⟨ front _ e ⟩
  col y w • col x w ∎
  where
  open Tools (n VRel,_===_)
  z : Bits n
  z = combine x y
  e : col x (col z w) ≈ col y w
  e = trans (col-col x z w) (Eq.subst (λ v → col (combine x z) w ≈ col v w) (combine-cancel x y) refl)
  col-• : ∀ (x : Bits n) a b → col x (a • b) ≈ col x a • col x b
  col-• x a b = sym (begin
    (negsB x • a • negsB x) • (negsB x • b • negsB x)
      ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • ((□ • □) • □ • □)) Eq.refl ⟩
    negsB x • a • ((negsB x • negsB x) • b • negsB x)
      ≈⟨ back _ (back _ (trans (front _ (negs² x)) left-unit)) ⟩
    negsB x • a • (b • negsB x)
      ≈⟨ back _ (sym assoc) ⟩
    negsB x • (a • b) • negsB x ∎)

-- The same against another circuit.
col-pair′ : ∀ (x y : Bits n) (w v : Circuit n) →
            (∀ z → n ⊢ w • col z v ≈ col z v • w) → n ⊢ col x w • col y v ≈ col y v • col x w
col-pair′ {n} x y w v h = begin
  col x w • col y v                    ≈⟨ back _ (sym e) ⟩
  col x w • col x (col z v)            ≈⟨ sym (col-•′ w (col z v)) ⟩
  col x (w • col z v)                  ≈⟨ back _ (front _ (h z)) ⟩
  col x (col z v • w)                  ≈⟨ col-•′ (col z v) w ⟩
  col x (col z v) • col x w            ≈⟨ front _ e ⟩
  col y v • col x w ∎
  where
  open Tools (n VRel,_===_)
  z : Bits n
  z = combine x y
  e : col x (col z v) ≈ col y v
  e = trans (col-col x z v) (Eq.subst (λ u → col (combine x z) v ≈ col u v) (combine-cancel x y) refl)
  col-•′ : ∀ a b → col x (a • b) ≈ col x a • col x b
  col-•′ a b = sym (begin
    (negsB x • a • negsB x) • (negsB x • b • negsB x)
      ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • ((□ • □) • □ • □)) Eq.refl ⟩
    negsB x • a • ((negsB x • negsB x) • b • negsB x)
      ≈⟨ back _ (back _ (trans (front _ (negs² x)) left-unit)) ⟩
    negsB x • a • (b • negsB x)
      ≈⟨ back _ (sym assoc) ⟩
    negsB x • (a • b) • negsB x ∎)

