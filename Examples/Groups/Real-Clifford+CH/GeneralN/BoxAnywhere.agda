------------------------------------------------------------------------
-- Presentations of groups
--
-- Two boxes anywhere, in any colours, commute (Clément, Lemma D.13,
-- Equations (335) and (336), placed)
--
-- `boxF u s` is the canonical box placed by a network u — its box wire
-- the wire u brings to wire 0 — and coloured by s (BoxFrames).  A
-- colouring passes a network with its bits permuted along the network
-- (`net-negs`, `swW`), and two colourings compose to one (`negs-xor`,
-- `combine`).  So two placed boxes with the same box wire are,
-- conjugated back by the network of one of them, the canonical box and
-- a colouring of it — (335) (`BoxComm.C335`) — and two with different
-- box wires, by a network bringing their box wires to the wires 0 and 1
-- (BoxFrames' σ-for), the canonical box and a colouring of the box on
-- wire 1 — (336).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.BoxAnywhere
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Fin using (Fin) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; X²)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; perm ; φ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires
  using (negsB ; negs² ; revS ; net-inv ; net-inv′ ; swapAt-negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames
  using (Canon ; module Frames ; pl ; pl-• ; pl-cong ; perm-• ; perm-σ₁)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (B₁ ; C335 ; C336)

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

------------------------------------------------------------------------
-- Placed boxes

module Anywhere {m : ℕ} (C : Canon m) (c335 : C335 m) (c336 : C336 m) where

  open Frames C

  private
    N : ℕ
    N = ₃₊ m

    Λ : Circuit N
    Λ = Λ□ (₂₊ m)

  open Tools (N VRel,_===_)

  private
    -- A placement undone.
    unpl : ∀ (w : Word (S.Gen N)) (a : Circuit N) → pl (revS w) (pl w a) ≈ a
    unpl w a = begin
      net (revS w) • (net w • a • net (revS w)) • net (revS (revS w))
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (net (revS w) • net w) • a • (net (revS w) • net (revS (revS w)))
        ≈⟨ cong (net-inv′ w) (back _ (net-inv (revS w))) ⟩
      ε • a • ε
        ≈⟨ trans left-unit right-unit ⟩
      a ∎

    repl : ∀ (w : Word (S.Gen N)) (a : Circuit N) → pl w (pl (revS w) a) ≈ a
    repl w a = begin
      net w • (net (revS w) • a • net (revS (revS w))) • net (revS w)
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (net w • net (revS w)) • a • (net (revS (revS w)) • net (revS w))
        ≈⟨ cong (net-inv w) (back _ (net-inv′ (revS w))) ⟩
      ε • a • ε
        ≈⟨ trans left-unit right-unit ⟩
      a ∎

    -- Commuting after a placement is commuting.
    by-pl : ∀ (w : Word (S.Gen N)) {a b : Circuit N} →
            pl (revS w) a • pl (revS w) b ≈ pl (revS w) b • pl (revS w) a → a • b ≈ b • a
    by-pl w {a} {b} e = begin
      a • b                                          ≈⟨ sym (repl w (a • b)) ⟩
      pl w (pl (revS w) (a • b))                     ≈⟨ pl-cong w (pl-• (revS w) a b) ⟩
      pl w (pl (revS w) a • pl (revS w) b)           ≈⟨ pl-cong w e ⟩
      pl w (pl (revS w) b • pl (revS w) a)           ≈⟨ pl-cong w (sym (pl-• (revS w) b a)) ⟩
      pl w (pl (revS w) (b • a))                     ≈⟨ repl w (b • a) ⟩
      b • a ∎

    -- A coloured placed box, placed back.
    back-box : ∀ (w : Word (S.Gen N)) (s : Bits N) (a : Circuit N) →
               pl (revS w) (negsB s • pl w a • negsB s) ≈ col (swW (revS w) s) a
    back-box w s a = begin
      pl (revS w) (negsB s • pl w a • negsB s)
        ≈⟨ trans (pl-• (revS w) (negsB s) _) (back _ (pl-• (revS w) (pl w a) (negsB s))) ⟩
      pl (revS w) (negsB s) • pl (revS w) (pl w a) • pl (revS w) (negsB s)
        ≈⟨ cong (net-negs (revS w) s) (cong (unpl w a) (net-negs (revS w) s)) ⟩
      col (swW (revS w) s) a ∎

    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

  -- Two boxes with the same box wire.
  same : ∀ (u u′ : Word (S.Gen N)) (t : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm u′ ⟨$⟩ʳ t ≡ 0F →
         (s s′ : Bits N) → boxF u s • boxF u′ s′ ≈ boxF u′ s′ • boxF u s
  same u u′ t pu pu′ s s′ = begin
    boxF u s • boxF u′ s′     ≈⟨ back _ e ⟩
    boxF u s • boxF u s′      ≈⟨ by-pl u (trans (cong (back-box u s Λ) (back-box u s′ Λ))
                                          (trans (col-pair (swW (revS u) s) (swW (revS u) s′) Λ c335)
                                                 (sym (cong (back-box u s′ Λ) (back-box u s Λ))))) ⟩
    boxF u s′ • boxF u s      ≈⟨ front _ (sym e) ⟩
    boxF u′ s′ • boxF u s ∎
    where
    e : boxF u′ s′ ≈ boxF u s′
    e = back _ (front _ (frame-eq u′ u t pu′ pu))

  -- Two boxes with different box wires.
  apart : ∀ (u u′ : Word (S.Gen N)) (t t′ : Fin N) → t′ ≢ t → perm u ⟨$⟩ʳ t ≡ 0F → perm u′ ⟨$⟩ʳ t′ ≡ 0F →
          (s s′ : Bits N) → boxF u s • boxF u′ s′ ≈ boxF u′ s′ • boxF u s
  apart u u′ t t′ t′≢t pu pu′ s s′ with σ-for u t′ t t′≢t pu
  ... | σ , σt , σt′ = begin
    boxF u s • boxF u′ s′
      ≈⟨ cong e₁ e₂ ⟩
    (negsB s • pl σ Λ • negsB s) • (negsB s′ • pl σ (B₁ m) • negsB s′)
      ≈⟨ by-pl σ (trans (cong (back-box σ s Λ) (back-box σ s′ (B₁ m)))
                  (trans (col-pair′ (swW (revS σ) s) (swW (revS σ) s′) Λ (B₁ m) c336)
                         (sym (cong (back-box σ s′ (B₁ m)) (back-box σ s Λ))))) ⟩
    (negsB s′ • pl σ (B₁ m) • negsB s′) • (negsB s • pl σ Λ • negsB s)
      ≈⟨ sym (cong e₂ e₁) ⟩
    boxF u′ s′ • boxF u s ∎
    where
    σ′ : Word (S.Gen N)
    σ′ = σ • S.σ
    pσ′ : perm σ′ ⟨$⟩ʳ t′ ≡ 0F
    pσ′ = Eq.trans (perm-• σ S.σ t′) (Eq.trans (Eq.cong (perm S.σ ⟨$⟩ʳ_) σt′) perm-σ₁)
    B-pl : pl σ′ Λ ≈ pl σ (B₁ m)
    B-pl = by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl
    e₁ : boxF u s ≈ negsB s • pl σ Λ • negsB s
    e₁ = back _ (front _ (frame-eq u σ t pu σt))
    e₂ : boxF u′ s′ ≈ negsB s′ • pl σ (B₁ m) • negsB s′
    e₂ = back _ (front _ (trans (frame-eq u′ σ′ t′ pu′ pσ′) B-pl))

  -- Any two placed boxes, in any colours.
  boxes-comm : ∀ (u u′ : Word (S.Gen N)) (t t′ : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm u′ ⟨$⟩ʳ t′ ≡ 0F →
               (s s′ : Bits N) → boxF u s • boxF u′ s′ ≈ boxF u′ s′ • boxF u s
  boxes-comm u u′ t t′ pu pu′ s s′ with t′ ≟ t
  ... | yes Eq.refl = same u u′ t pu pu′ s s′
  ... | no  t′≢t    = apart u u′ t t′ t′≢t pu pu′ s s′
