------------------------------------------------------------------------
-- Presentations of groups
--
-- Coloured gates placed by swap networks (Clément, Appendix E.5)
--
-- Every decoded letter of Figure 8 is a gate at the canonical position,
-- placed by a network and coloured: `place u s g = col s (pl u g)`.  A
-- gate is *rigid* on its bottom k wires when every network above them
-- passes it; its placement then depends on the network only through
-- those k wires (`frame`, LocalPlace's `place-eq` with the rigidity as
-- a hypothesis).  To prove a statement about placed gates, conjugate by
-- one network that brings their significant wires to the bottom: a
-- placement composes (`pl-pl`), a colouring passes a network with its
-- bits permuted (`pl-col`), and the bit of the permuted colouring at a
-- wire is read off where the network sends it (`swW-lookup`), so only
-- a few bits of the colourings ever need naming.  `By σ` is conjugation
-- by the inverse of σ, an automorphism (`reflect`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Placed where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _<_ ; s≤s ; z≤n)
open import Data.Product using (Σ ; _×_ ; _,_)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; perm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires
  using (negsB ; negs² ; revS ; net-inv ; net-inv′ ; perm-inv ; perm-inj ; sdS ; sd-target)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames
  using (pl ; pl-cong ; pl-• ; perm-• ; perm-↑0 ; perm-↑s)
open import Examples.Groups.Real-Clifford+CH.GeneralN.LocalPlace using (up ; lift-k)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (swG ; swW ; net-negs ; combine ; _⇔_ ; col-col)

-- Colours are the parameter-free ones of Col (through Colours).
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)

private
  variable
    n r : ℕ

------------------------------------------------------------------------
-- Networks

-- The reverse of a network is an involution.
revS² : ∀ (w : Word (S.Gen n)) → revS (revS w) ≡ w
revS² [ g ]ʷ  = Eq.refl
revS² ε       = Eq.refl
revS² (u • v) = Eq.cong₂ _•_ (revS² u) (revS² v)

-- Where the inverse sends the image.
perm-back : ∀ (w : Word (S.Gen n)) {t j : Fin n} → perm w ⟨$⟩ʳ t ≡ j → perm (revS w) ⟨$⟩ʳ j ≡ t
perm-back w {t} e = Eq.trans (Eq.cong (perm (revS w) ⟨$⟩ʳ_) (Eq.sym e)) (perm-inv w t)

------------------------------------------------------------------------
-- Rigid gates and frames

-- Every network above the bottom k wires passes g.
Rigid : ∀ k → Circuit (k + r) → Set
Rigid {r} k g = ∀ (v : Word (S.Gen r)) → (k + r) ⊢ up k (net v) • g ≈ g • up k (net v)

-- A rigid gate placed by two networks that agree on its wires.
frame : ∀ {k} {g : Circuit (k + r)} → Rigid k g → (σ σ′ : Word (S.Gen (k + r))) →
        (∀ (j : Fin (k + r)) → toℕ j < k → perm σ′ ⟨$⟩ʳ (perm (revS σ) ⟨$⟩ʳ j) ≡ j) →
        (k + r) ⊢ pl σ g ≈ pl σ′ g
frame {r} {k} {g} rig σ σ′ agree with lift-k k (revS σ • σ′) agree
... | v , e = sym (begin
  net σ′ • g • net (revS σ′)
    ≈⟨ sym left-unit ⟩
  ε • (net σ′ • g • net (revS σ′))
    ≈⟨ front _ (sym (net-inv σ)) ⟩
  (net σ • net (revS σ)) • (net σ′ • g • net (revS σ′))
    ≈⟨ by-passoc ((□ • □) • (□ • □ • □)) (□ • ((□ • □) • □) • □) Eq.refl ⟩
  net σ • ((net (revS σ) • net σ′) • g) • net (revS σ′)
    ≈⟨ back _ (front _ (trans (front _ e) (rig v))) ⟩
  net σ • (g • up k (net v)) • net (revS σ′)
    ≈⟨ back _ (front _ (back _ (sym e))) ⟩
  net σ • (g • (net (revS σ) • net σ′)) • net (revS σ′)
    ≈⟨ by-passoc (□ • (□ • (□ • □)) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
  net σ • g • net (revS σ) • (net σ′ • net (revS σ′))
    ≈⟨ back _ (back _ (trans (back _ (net-inv σ′)) right-unit)) ⟩
  net σ • g • net (revS σ) ∎)
  where open Tools ((k + r) VRel,_===_)

-- The same for a gate rigid on one wire: only wire 0 counts.
frame₁ : ∀ {g : Circuit (₁₊ r)} → Rigid 1 g → (σ σ′ : Word (S.Gen (₁₊ r))) →
         perm σ′ ⟨$⟩ʳ (perm (revS σ) ⟨$⟩ʳ 0F) ≡ 0F → (₁₊ r) ⊢ pl σ g ≈ pl σ′ g
frame₁ rig σ σ′ e = frame rig σ σ′ agree
  where
  agree : ∀ j → toℕ j < 1 → perm σ′ ⟨$⟩ʳ (perm (revS σ) ⟨$⟩ʳ j) ≡ j
  agree 0F     _             = e
  agree (sF j) (s≤s ())

------------------------------------------------------------------------
-- Placements compose, and colourings pass them

module _ {n : ℕ} where
  open Tools (n VRel,_===_)

  pl-pl : ∀ (a b : Word (S.Gen n)) (g : Circuit n) → pl a (pl b g) ≈ pl (a • b) g
  pl-pl a b g = by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl

  pl-col : ∀ (w : Word (S.Gen n)) (s : Bits n) (g : Circuit n) → pl w (col s g) ≈ col (swW w s) (pl w g)
  pl-col w s g = trans (pl-• w (negsB s) _) (trans (back _ (pl-• w g (negsB s)))
                   (trans (cong (net-negs w s) (back _ (net-negs w s)))
                          refl))

  -- A placement undone.
  unpl : ∀ (w : Word (S.Gen n)) (a : Circuit n) → pl (revS w) (pl w a) ≈ a
  unpl w a = begin
    net (revS w) • (net w • a • net (revS w)) • net (revS (revS w))
      ≈⟨ back _ (back _ (≡→≈ (Eq.cong net (revS² w)))) ⟩
    net (revS w) • (net w • a • net (revS w)) • net w
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (net (revS w) • net w) • a • (net (revS w) • net w)
      ≈⟨ cong (net-inv′ w) (back _ (net-inv′ w)) ⟩
    ε • a • ε
      ≈⟨ trans left-unit right-unit ⟩
    a ∎
    where
    ≡→≈ : ∀ {p q : Circuit n} → p ≡ q → p ≈ q
    ≡→≈ Eq.refl = refl

  -- A commutation carried by a placement, and back.
  pl-comm : ∀ (w : Word (S.Gen n)) {a b : Circuit n} → a • b ≈ b • a → pl w a • pl w b ≈ pl w b • pl w a
  pl-comm w e = trans (sym (pl-• w _ _)) (trans (pl-cong w e) (pl-• w _ _))

  reflect : ∀ (w : Word (S.Gen n)) {a b : Circuit n} →
            pl (revS w) a • pl (revS w) b ≈ pl (revS w) b • pl (revS w) a → a • b ≈ b • a
  reflect w {a} {b} e = begin
    a • b                                          ≈⟨ sym (cong (unpl′ a) (unpl′ b)) ⟩
    pl w (pl (revS w) a) • pl w (pl (revS w) b)    ≈⟨ pl-comm w e ⟩
    pl w (pl (revS w) b) • pl w (pl (revS w) a)    ≈⟨ cong (unpl′ b) (unpl′ a) ⟩
    b • a ∎
    where
    unpl′ : ∀ c → pl w (pl (revS w) c) ≈ c
    unpl′ c = Eq.subst (λ v → pl v (pl (revS w) c) ≈ c) (revS² w) (unpl (revS w) c)

------------------------------------------------------------------------
-- Colourings placed

private
  ⇔-cancel : ∀ a b → (a ⇔ (a ⇔ b)) ≡ b
  ⇔-cancel true  b     = Eq.refl
  ⇔-cancel false true  = Eq.refl
  ⇔-cancel false false = Eq.refl

  combine-cancel : ∀ (x y : Bits n) → combine x (combine x y) ≡ y
  combine-cancel []      []      = Eq.refl
  combine-cancel (a ∷ x) (b ∷ y) = Eq.cong₂ _∷_ (⇔-cancel a b) (combine-cancel x y)

place : Word (S.Gen n) → Bits n → Circuit n → Circuit n
place u s g = col s (pl u g)

module _ {n : ℕ} where
  open Tools (n VRel,_===_)

  -- Placing a placed gate.
  place-pl : ∀ (w u : Word (S.Gen n)) (s : Bits n) (g : Circuit n) →
             pl w (place u s g) ≈ place (w • u) (swW w s) g
  place-pl w u s g = trans (pl-col w s (pl u g)) (mid _ _ (pl-pl w u g))

  -- Two colourings of commuting gates: only the relative colouring counts.
  col-rel : ∀ (x y : Bits n) {w v : Circuit n} →
            w • col (combine x y) v ≈ col (combine x y) v • w → col x w • col y v ≈ col y v • col x w
  col-rel x y {w} {v} h = Cx.⟪⟫-≈ h (Cx.⟪⟫-•₂ refl e) (Cx.⟪⟫-•₂ e refl)
    where
    module Cx = Conj {n} (negsB x) (negs² x)
    e : Cx.⟪ col (combine x y) v ⟫ ≈ col y v
    e = trans (col-col x (combine x y) v)
              (Eq.subst (λ u → col (combine x (combine x y)) v ≈ col u v) (combine-cancel x y) refl)

------------------------------------------------------------------------
-- Reading a bit of a colouring through a network

private
  swG-lookup : ∀ (g : S.Gen n) (s : Bits n) (j : Fin n) →
               lookupℕ (toℕ j) (swG g s) ≡ lookupℕ (toℕ (perm [ g ]ʷ ⟨$⟩ʳ j)) s
  swG-lookup (S.gate₀ ())
  swG-lookup (S.gate₁ ())
  swG-lookup (S.gate₂ S.σ-gate) (a ∷ b ∷ t) 0F          = Eq.refl
  swG-lookup (S.gate₂ S.σ-gate) (a ∷ b ∷ t) (sF 0F)     = Eq.refl
  swG-lookup (S.gate₂ S.σ-gate) (a ∷ b ∷ t) (sF (sF j)) = Eq.refl
  swG-lookup (g S.↥)            (a ∷ t)     0F          = Eq.refl
  swG-lookup (g S.↥)            (a ∷ t)     (sF j)      = swG-lookup g t j

swW-lookup : ∀ (w : Word (S.Gen n)) (s : Bits n) (j : Fin n) →
             lookupℕ (toℕ j) (swW w s) ≡ lookupℕ (toℕ (perm w ⟨$⟩ʳ j)) s
swW-lookup [ g ]ʷ  s j = swG-lookup g s j
swW-lookup ε       s j = Eq.refl
swW-lookup (u • v) s j = Eq.trans (swW-lookup u (swW v s) j) (swW-lookup v s (perm u ⟨$⟩ʳ j))

-- The bit of a relative colouring.
combine-lookup : ∀ i (x y : Bits n) → i < n → lookupℕ i (combine x y) ≡ (lookupℕ i x ⇔ lookupℕ i y)
combine-lookup i       []      []      ()
combine-lookup zero    (a ∷ x) (b ∷ y) _       = Eq.refl
combine-lookup (suc i) (a ∷ x) (b ∷ y) (s≤s p) = combine-lookup i x y p

⇔-same : ∀ b → (b ⇔ b) ≡ true
⇔-same true  = Eq.refl
⇔-same false = Eq.refl

⇔-diff : ∀ a b → a ≢ b → (a ⇔ b) ≡ false
⇔-diff true  true  ne = ⊥-elim (ne Eq.refl)
⇔-diff true  false _  = Eq.refl
⇔-diff false true  _  = Eq.refl
⇔-diff false false ne = ⊥-elim (ne Eq.refl)

------------------------------------------------------------------------
-- Networks bringing two or three wires to the bottom

-- Abstract, like BoxFrames' σ-for: clients match on the triple.
abstract
  bring₁ : (t : Fin (₁₊ n)) → Σ (Word (S.Gen (₁₊ n))) λ σ → perm σ ⟨$⟩ʳ t ≡ 0F
  bring₁ t = sdS (toℕ t) , sd-target t

  -- t to wire 0 and t′ to wire 1.
  bring₂ : (t t′ : Fin (₂₊ n)) → t′ ≢ t →
           Σ (Word (S.Gen (₂₊ n))) λ σ → (perm σ ⟨$⟩ʳ t ≡ 0F) × (perm σ ⟨$⟩ʳ t′ ≡ sF 0F)
  bring₂ {n} t t′ ne = go (perm u ⟨$⟩ʳ t′) Eq.refl
    where
    u : Word (S.Gen (₂₊ n))
    u = sdS (toℕ t)
    go : ∀ x → perm u ⟨$⟩ʳ t′ ≡ x →
         Σ (Word (S.Gen (₂₊ n))) λ σ → (perm σ ⟨$⟩ʳ t ≡ 0F) × (perm σ ⟨$⟩ʳ t′ ≡ sF 0F)
    go 0F     e = ⊥-elim (ne (perm-inj u (Eq.trans e (Eq.sym (sd-target t)))))
    go (sF x) e = u • (sdS (toℕ x) S.↑) , σt , σt′
      where
      σt : perm (u • (sdS (toℕ x) S.↑)) ⟨$⟩ʳ t ≡ 0F
      σt = Eq.trans (Eq.cong (perm (sdS (toℕ x) S.↑) ⟨$⟩ʳ_) (sd-target t)) (perm-↑0 (sdS (toℕ x)))
      σt′ : perm (u • (sdS (toℕ x) S.↑)) ⟨$⟩ʳ t′ ≡ sF 0F
      σt′ = Eq.trans (Eq.cong (perm (sdS (toℕ x) S.↑) ⟨$⟩ʳ_) e)
                     (Eq.trans (perm-↑s (sdS (toℕ x)) x) (Eq.cong sF (sd-target x)))

  -- t, t′, j to the wires 0, 1, 2.
  bring₃ : (t t′ j : Fin (₃₊ n)) → t′ ≢ t → j ≢ t → j ≢ t′ →
           Σ (Word (S.Gen (₃₊ n))) λ σ →
             (perm σ ⟨$⟩ʳ t ≡ 0F) × (perm σ ⟨$⟩ʳ t′ ≡ sF 0F) × (perm σ ⟨$⟩ʳ j ≡ sF (sF 0F))
  bring₃ {n} t t′ j t′t jt jt′ with bring₂ t t′ t′t
  ... | σ , σt , σt′ = go (perm σ ⟨$⟩ʳ j) Eq.refl
    where
    go : ∀ x → perm σ ⟨$⟩ʳ j ≡ x →
         Σ (Word (S.Gen (₃₊ n))) λ ρ →
           (perm ρ ⟨$⟩ʳ t ≡ 0F) × (perm ρ ⟨$⟩ʳ t′ ≡ sF 0F) × (perm ρ ⟨$⟩ʳ j ≡ sF (sF 0F))
    go 0F          e = ⊥-elim (jt (perm-inj σ (Eq.trans e (Eq.sym σt))))
    go (sF 0F)     e = ⊥-elim (jt′ (perm-inj σ (Eq.trans e (Eq.sym σt′))))
    go (sF (sF x)) e = σ • ((sdS (toℕ x) S.↑) S.↑) , ρt , ρt′ , ρj
      where
      v : Word (S.Gen (₃₊ n))
      v = (sdS (toℕ x) S.↑) S.↑
      ρt : perm (σ • v) ⟨$⟩ʳ t ≡ 0F
      ρt = Eq.trans (Eq.cong (perm v ⟨$⟩ʳ_) σt) (perm-↑0 (sdS (toℕ x) S.↑))
      ρt′ : perm (σ • v) ⟨$⟩ʳ t′ ≡ sF 0F
      ρt′ = Eq.trans (Eq.cong (perm v ⟨$⟩ʳ_) σt′)
                     (Eq.trans (perm-↑s (sdS (toℕ x) S.↑) 0F) (Eq.cong sF (perm-↑0 (sdS (toℕ x)))))
      ρj : perm (σ • v) ⟨$⟩ʳ j ≡ sF (sF 0F)
      ρj = Eq.trans (Eq.cong (perm v ⟨$⟩ʳ_) e)
                    (Eq.trans (perm-↑s (sdS (toℕ x) S.↑) (sF x))
                              (Eq.cong sF (Eq.trans (perm-↑s (sdS (toℕ x)) x) (Eq.cong sF (sd-target x)))))
